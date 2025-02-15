import {
  buildCloseNodeTag,
  buildGapTag,
  buildOpenNodeTag,
  buildReferenceTag,
  buildStubNode,
  isFragmentNode,
  isNullNode,
  parseReference,
  referenceFlags,
} from '@bablr/agast-helpers/tree';
import { getStreamIterator } from '@bablr/agast-helpers/stream';
import { agast } from '@bablr/agast-vm';
import * as btree from '@bablr/agast-helpers/btree';
import { Pump } from './utils/pump.js';
import { OpenNodeTag, ReferenceTag } from '@bablr/agast-helpers/symbols';
import { get, getProperties } from '@bablr/agast-helpers/path';
import { isArray } from '@bablr/helpers/object';

export const states = new WeakMap();
export const internalStates = new WeakMap();

const { hasOwn } = Object;

const buildFullRange = (node) => {
  const sum = btree.getSum(node.children);
  return sum ? [0, sum - 1] : null;
};

export const FragmentFacade = class BABLRFragmentFacade {
  static wrap(
    node,
    context,
    transparent = false,
    childrenIndexRange = node && buildFullRange(node),
    dotPropertyName = null,
    dotPropertyIndex = null,
  ) {
    return (
      node &&
      new FragmentFacade(
        node,
        context,
        transparent,
        childrenIndexRange,
        dotPropertyName,
        dotPropertyIndex,
      )
    );
  }

  constructor(node, context, transparent, childrenIndexRange, dotPropertyName, dotPropertyIndex) {
    if (childrenIndexRange && (childrenIndexRange[0] == null || !childrenIndexRange[1] == null)) {
      throw new Error();
    }

    if (!context) throw new Error();

    if (dotPropertyName && !hasOwn(node.properties, dotPropertyName)) throw new Error();

    if (isArray(node.properties[dotPropertyName]) && dotPropertyIndex == null) throw new Error();

    states.set(this, {
      context,
      openTag: buildOpenNodeTag(),
      closeTag: buildCloseNodeTag(),
      node,
      transparent,
      childrenIndexRange,
      dotPropertyName,
      dotPropertyIndex,
    });
  }

  get isTransparent() {
    return states.get(this).transparent;
  }

  get isFragmentNode() {
    return isFragmentNode(states.get(this).node);
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

    return openTag.type === OpenNodeTag ? openTag.value.flags : null;
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
    let {
      node,
      context,
      transparent,
      dotPropertyName,
      dotPropertyIndex: dotIndex,
    } = states.get(this);
    // let { path: nodePath } = internalStates.get(node);
    const parsedRef = parseReference(path);
    // const resolvedPath = resolvePath(node, path);
    // const childNode = getAtPath(resolvedPath, node);

    // array resolve

    if (dotPropertyName) {
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

    return isNullNode(node_) ? null : FragmentFacade.wrap(node_, context, transparent);
  }

  has(path) {
    return hasOwn(states.get(this).node.properties, parseReference(path).value.name);
  }
};

Object.seal(FragmentFacade);

export const buildInternalState = () => {
  let instructionsPump = new Pump();
  let expressionsPump = new Pump();
  let agastState = null;
  let agast_ = getStreamIterator(
    agast(
      (ctx, s) => {
        agastState = s;
        return instructionsPump;
      },
      { expressions: expressionsPump },
    ),
  );
  let internalState = {
    instructionsPump,
    expressionsPump,
    agastState,
    agast: agast_,
    path: agastState.path,
  };
  return internalState;
};
