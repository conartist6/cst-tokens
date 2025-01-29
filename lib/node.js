import { OpenFragmentTag, OpenNodeTag, ReferenceTag } from '@bablr/agast-helpers/symbols';
import {
  buildFragmentCloseTag,
  buildFragmentOpenTag,
  buildGapTag,
  buildReferenceTag,
  buildStubNode,
  referenceFlags,
} from '@bablr/agast-helpers/tree';
import { parseRef } from '@bablr/agast-helpers/shorthand';
import * as btree from '@bablr/agast-helpers/btree';
import { get, getProperties } from '@bablr/agast-helpers/path';
import { getStreamIterator } from '@bablr/agast-helpers/stream';
import { agast } from '@bablr/agast-vm';
import { createPassthroughStrategy } from '@bablr/agast-vm-strategy-passthrough';
import { Pump } from './utils/pump.js';

const { hasOwn } = Object;

export const internalStates = new WeakMap();

export const states = new WeakMap();

const buildFullRange = (node) => {
  const sum = btree.getSum(node.children);
  return sum ? [0, sum - 1] : null;
};

export const FragmentFacade = class BABLRFragmentFacade {
  static wrap(
    node,
    context,
    transparent = false,
    childrenIndexRange = buildFullRange(node),
    dotPropertyName = null,
  ) {
    if (!context || !node) throw new Error();

    return (
      node && new FragmentFacade(node, context, transparent, childrenIndexRange, dotPropertyName)
    );
  }

  constructor(node, context, transparent, childrenIndexRange, dotPropertyName) {
    if (childrenIndexRange && (childrenIndexRange[0] == null || !childrenIndexRange[1] == null)) {
      throw new Error();
    }

    states.set(this, {
      context,
      openTag: buildFragmentOpenTag(),
      closeTag: buildFragmentCloseTag(),
      node,
      transparent,
      childrenIndexRange,
      dotPropertyName,
    });
  }

  get isTransparent() {
    return states.get(this).transparent;
  }

  get children() {
    const { node, transparent, childrenIndexRange } = states.get(this);

    return {
      *[Symbol.iterator]() {
        for (let i = childrenIndexRange[0]; i <= childrenIndexRange[1]; i++) {
          const interpolated = false; // TODO
          if (!interpolated || transparent) {
            yield btree.getAt(i, node.children);
          }
        }
      },
    };
  }

  getRootIndex() {
    const { node, dotPropertyName, childrenIndexRange } = states.get(this);

    if (!childrenIndexRange) return null;

    if (childrenIndexRange[0] > childrenIndexRange[1]) throw new Error();

    for (let i = childrenIndexRange[0]; i <= childrenIndexRange[1]; i++) {
      let tag = btree.getAt(i, node.children);
      if (tag.type === ReferenceTag) {
        const { name, isArray } = tag.value;
        let resolvedTagName = name === '.' ? dotPropertyName : name;

        if (resolvedTagName === dotPropertyName) {
          return i;
        }
      }
    }

    return null;
  }

  get flags() {
    const { openTag } = this;

    return openTag.type === OpenNodeTag
      ? openTag.value.flags
      : openTag.type === OpenFragmentTag
      ? // redundant value accessor for monomorphism
        openTag.value.flags
      : null;
  }

  get language() {
    let { node } = states.get(this);

    return node.language;
  }

  get type() {
    let { node } = states.get(this);

    return node.type;
  }

  get attributes() {
    let { node } = states.get(this);

    return node.attributes;
  }

  get openTag() {
    const state = states.get(this);
    const { children } = state.node;

    return state.openTag || btree.getAt(0, children);
  }

  get closeTag() {
    const state = states.get(this);
    const { children } = state.node;

    return state.closeTag || btree.getAt(btree.getSum(children) - 1, children);
  }

  get(path) {
    let { node, context, transparent, dotPropertyName } = states.get(this);
    let { path: nodePath } = internalStates.get(node);
    const parsedRef = parseRef(path);
    // const resolvedPath = resolvePath(node, path);
    // const childNode = getAtPath(resolvedPath, node);

    // array resolve

    if (dotPropertyName) {
      let dotChildrenIndex = this.getRootIndex();
      let dotIndex = nodePath.referenceIndexes[dotChildrenIndex];
      let dotReference = buildReferenceTag(
        dotPropertyName,
        dotIndex != null,
        referenceFlags,
        dotIndex,
      );

      node = get(dotReference, node);
    }

    const binding = getProperties(parsedRef, node.properties);

    if (!binding) return null;

    const ref = binding.reference;

    const node_ =
      (ref && ref.type === ReferenceTag && !ref.value.flags.hasGap) || transparent
        ? binding.node
        : buildStubNode(buildGapTag());

    return FragmentFacade.wrap(node_, context, transparent);
  }

  has(path) {
    return hasOwn(states.get(this).node.properties, parseRef(path).value.name);
  }
};

Object.seal(FragmentFacade);

export const buildInternalState = () => {
  let agastPump = new Pump();
  let expressionsPump = new Pump();
  let agastState = null;
  let agast_ = getStreamIterator(
    agast(
      (ctx, s) => {
        agastState = s;
        return createPassthroughStrategy(agastPump)(ctx, s);
      },
      { expressions: expressionsPump },
    ),
  );
  let internalState = {
    agastPump,
    expressionsPump,
    agastState,
    agast: agast_,
    path: agastState.path,
  };
  return internalState;
};
