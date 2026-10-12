import * as t from "@babel/types";

import {
  semanticStaticPropertyKey,
  semanticWriteTargets,
  unwrapJavaScriptExpression,
} from "./javascriptAstValues.js";
import { traverseJavaScriptAstSteps } from "./javascriptSemanticTraversal.js";

/** Match Electron's supported module entry points. */
export const ELECTRON_MODULE =
  /^electron(?:\/(?:common|main|renderer|utility))?$/u;

/**
 * Electron's CommonJS exports define no `default` member, so a leading
 * `default` segment can only denote the module object itself, as an ES module
 * default import (`import electron from "electron"`) binds it.
 */
export const electronExportPath = (
  importedPath: readonly string[],
): readonly string[] =>
  importedPath[0] === "default" ? importedPath.slice(1) : importedPath;

/** Static identity recovery cannot establish the absence of Electron usage. */
export const ELECTRON_IDENTITY_LIMITATION =
  "Electron API identity follows proven lexical module aliases and structurally verified module-namespace interop. Other reassignments, dynamic selections, and visibly overwritten namespace members are unresolved; missing findings do not establish absence. Arbitrary call side effects and runtime registration are not evaluated.";

/** Preserve exact property segments instead of flattening literal dotted keys. */
export const electronMemberPath = (
  node: t.Node,
): {
  readonly root: t.Node;
  readonly members: readonly (string | null)[];
} => {
  let root = unwrapJavaScriptExpression(node).node;
  const members: (string | null)[] = [];
  while (t.isMemberExpression(root) || t.isOptionalMemberExpression(root)) {
    members.push(semanticStaticPropertyKey(root.property, root.computed));
    root = unwrapJavaScriptExpression(root.object).node;
  }
  return { root, members: members.toReversed() };
};

/** A known intrinsic callable and its examined positional arguments. */
export interface JavaScriptIntrinsicInvocation {
  readonly kind: "known" | "opaque";
  /** The original bound receiver; rebinding cannot replace it. */
  readonly receiver?: t.Node;
  readonly path: readonly string[];
  readonly arguments:
    | readonly t.CallExpression["arguments"][number][]
    | undefined;
}

/** Ordered property effects of an already-proven intrinsic invocation. */
export interface JavaScriptIntrinsicMutation {
  readonly site: t.CallExpression | t.OptionalCallExpression;
  readonly target: t.Node;
  readonly path: readonly (string | null)[];
  readonly value?: t.Node;
  readonly operation:
    | "value"
    | "delete"
    | "descriptor"
    | "copy"
    | "descriptors"
    | "identity";
  readonly readAt: t.Node;
  readonly returnsTarget: boolean;
  readonly dispatchTarget?: t.Node;
  readonly definite: boolean;
}

const intrinsicMutationEffects = (
  site: t.CallExpression | t.OptionalCallExpression,
  invocation: JavaScriptIntrinsicInvocation,
  staticString: (node: t.Node | undefined) => string | undefined,
): readonly JavaScriptIntrinsicMutation[] => {
  const args = invocation.arguments;
  if (!args || args.some(t.isSpreadElement)) return [];
  const method = invocation.path.at(-1);
  const owner = invocation.path[1];
  const target =
    owner === "Reflect" && method === "set" && args.length >= 4
      ? args[3]
      : args[0];
  if (!t.isNode(target)) return [];
  const effects: JavaScriptIntrinsicMutation[] = [];
  const readAt = site.arguments.at(-1) ?? site.callee;
  const retain = (
    operation: JavaScriptIntrinsicMutation["operation"],
    key: string | null,
    value: t.Node | undefined,
  ): void => {
    effects.push({
      site,
      target,
      path: [key],
      ...(value === undefined ? {} : { value }),
      operation,
      readAt,
      returnsTarget: owner === "Object",
      ...(owner === "Reflect" &&
      method === "set" &&
      args.length >= 4 &&
      t.isNode(args[0])
        ? { dispatchTarget: args[0] }
        : {}),
      definite:
        key !== null || operation === "copy" || operation === "descriptors",
    });
  };
  const key = staticString(args[1]) ?? null;
  if (method === "set") retain("value", key, args[2]);
  else if (method === "deleteProperty") retain("delete", key, undefined);
  else if (method === "defineProperty") retain("descriptor", key, args[2]);
  else if (method === "assign") {
    for (const source of args.slice(1)) retain("copy", null, source);
  } else if (method === "defineProperties")
    retain("descriptors", null, args[1]);
  if (effects.length === 0) retain("identity", null, undefined);
  // Prototype changes do not replace known own properties. Source objects and
  // descriptors retain their syntax for the shared symbolic property owner.
  return effects;
};

/** Index writes through caller-proven identities of bindings and receiver values. */
export function* collectJavaScriptIdentityWritesSteps(
  program: t.Program,
  origin: (
    target: t.Node,
    kind: "binding" | "member" | "opaque-call",
  ) => readonly (readonly (string | null)[])[],
  intrinsicInvocation: (
    node: t.CallExpression | t.OptionalCallExpression,
  ) => JavaScriptIntrinsicInvocation | undefined,
  staticString: (node: t.Node | undefined) => string | undefined,
  freshObject: (node: t.Node) => boolean,
  retain: (node: t.Node, path: readonly (string | null)[]) => void,
  retainMutation?: (mutation: JavaScriptIntrinsicMutation) => void,
): Generator<void> {
  const objectMutators = new Set([
    "defineProperty",
    "defineProperties",
    "assign",
    "setPrototypeOf",
  ]);
  const reflectMutators = new Set([
    "set",
    "deleteProperty",
    "defineProperty",
    "setPrototypeOf",
  ]);
  const keyedMutators = new Set(["set", "deleteProperty", "defineProperty"]);
  yield* traverseJavaScriptAstSteps(program, {
    enter: (node) => {
      if (t.isCallExpression(node) || t.isOptionalCallExpression(node)) {
        const invocation = intrinsicInvocation(node);
        if (invocation?.kind === "opaque") {
          for (const scope of origin(node, "opaque-call")) retain(node, scope);
          return;
        }
        const callee = invocation?.path;
        const arguments_ = invocation?.arguments;
        const method = callee?.at(-1);
        const owner = callee?.length === 3 ? callee[1] : undefined;
        if (
          (owner === "Object" && objectMutators.has(method ?? "")) ||
          (owner === "Reflect" && reflectMutators.has(method ?? ""))
        ) {
          if (invocation && retainMutation)
            for (const effect of intrinsicMutationEffects(
              node,
              invocation,
              staticString,
            ))
              retainMutation(effect);
          // Reflect.set can write through its explicit receiver as well as
          // dispatching through its target. Both identities need examination.
          const targets =
            owner === "Reflect" &&
            method === "set" &&
            arguments_ !== undefined &&
            (arguments_.length >= 4 || arguments_.some(t.isSpreadElement))
              ? [
                  arguments_[0],
                  arguments_.some(t.isSpreadElement)
                    ? undefined
                    : arguments_[3],
                ]
              : [arguments_?.[0]];
          for (const target of targets) {
            // A known mutator with an opaque argument list can overwrite any
            // captured intrinsic. Do not turn an unexamined target into proof.
            if (target === undefined || t.isSpreadElement(target)) {
              for (const scope of origin(node, "opaque-call"))
                retain(node, scope);
            }
            if (t.isNode(target) && !t.isSpreadElement(target)) {
              const exports = origin(target, "member");
              if (exports.length > 0) {
                const key = keyedMutators.has(method ?? "")
                  ? [staticString(arguments_?.[1]) ?? null]
                  : [];
                for (const exported of exports)
                  retain(node, [...exported, ...key]);
              } else if (!freshObject(target)) {
                for (const scope of origin(node, "opaque-call"))
                  retain(node, scope);
              }
            }
          }
        }
      }
      const target = t.isAssignmentExpression(node)
        ? node.left
        : t.isUpdateExpression(node)
          ? node.argument
          : t.isUnaryExpression(node, { operator: "delete" })
            ? node.argument
            : t.isForOfStatement(node) || t.isForInStatement(node)
              ? node.left
              : undefined;
      if (target === undefined) return;
      for (const leaf of semanticWriteTargets(target)) {
        if (t.isIdentifier(leaf)) {
          for (const exported of origin(leaf, "binding"))
            retain(node, exported);
          continue;
        }
        // Replacing a container slot does not mutate the value previously in
        // that slot. Resolve its receiver, then append the written key once.
        const key = semanticStaticPropertyKey(leaf.property, leaf.computed);
        for (const exported of origin(leaf.object, "member"))
          retain(node, [...exported, key]);
      }
    },
  });
}
