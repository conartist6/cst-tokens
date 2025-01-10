import { Coroutine } from '@bablr/coroutine';
import { buildOpenNodeTag, buildWriteEffect } from '@bablr/agast-helpers/builders';
import { getStreamIterator, isEmpty, StreamIterable } from '@bablr/agast-helpers/stream';
import { formatType } from './utils/format.js';
import { facades } from './facades.js';
import { nodeStates, State } from './state.js';
import { updateSpans } from './spans.js';
import {
  OpenNodeTag,
  CloseNodeTag,
  ShiftTag,
  GapTag,
  LiteralTag,
  ReferenceTag,
  OpenFragmentTag,
  DoctypeTag,
  NullTag,
} from '@bablr/agast-helpers/symbols';
import { NodeFacade } from './node.js';
import { getOpenTag, treeFromStreamSync } from '@bablr/agast-helpers/tree';
import * as btree from '@bablr/agast-helpers/btree';
import { getEmbeddedTag } from '@bablr/agast-vm-helpers/deembed';
import { Match } from './match.js';
import { reifyExpression, shouldBranch } from '@bablr/agast-vm-helpers';
import { allTagsFor, TagPath } from '@bablr/agast-helpers/path';

const bindAttribute = (m, s, key, value) => {
  const openTag = getOpenTag(m.node);

  if (value != null) {
    const { flags, language, type } = openTag.value;
    const attributes = { ...openTag.value.attributes, [key]: value };
    const newOpenTag = buildOpenNodeTag(flags, language, type, attributes);

    m.node.attributes = attributes;

    // if (openNext) {
    // } else {
    //   // could this tag be stored anywhere else?
    //   s.result = newOpenTag;
    // }

    m.node.children = btree.replaceAt(0, m.node.children, newOpenTag);
  }

  nodeStates.get(m.node).unboundAttributes.delete(key);
};

const getSourceLength = (tags) => {
  let i = 0;
  for (const tag of tags) {
    if (tag.type === LiteralTag) {
      i += tag.value.length;
    } else if (tag.type === GapTag) {
      i += 1;
    }
  }
  return i;
};

export const bablr = (ctx, rootSource, strategy, options = {}) => {
  return new StreamIterable(__bablr(ctx, rootSource, strategy, options));
};

function* __bablr(ctx, rootSource, strategy, options) {
  let s = State.from(rootSource, ctx);
  let m = null;
  let language = null;

  let co = new Coroutine(getStreamIterator(strategy(facades.get(s), facades.get(ctx))));

  co.advance();

  {
    s.source.advance();

    const sourceStep = s.source.fork.head.step;

    if (sourceStep instanceof Promise) {
      yield sourceStep;
    }
  }

  for (;;) {
    if (co.current instanceof Promise) {
      co.current = yield co.current;
    }

    if (co.done) break;

    const instr = co.value;
    let returnValue = undefined;

    const { verb } = instr;

    switch (verb) {
      case 'init': {
        let { arguments: { 0: canonicalURL } = [] } = instr;

        if (language !== null) throw new Error();

        language = ctx.languages.get(canonicalURL);
        break;
      }

      case 'advance': {
        const { arguments: { 0: embeddedTags } = [] } = instr;

        const tag = getEmbeddedTag(embeddedTags);

        switch (tag.type) {
          case DoctypeTag: {
            m.advance(tag);

            m.rangePreviousIndex = 0;
            break;
          }

          case ReferenceTag: {
            m.advance(tag);

            s.referenceTagPath = m.parent ? TagPath.from(m.parent.path, -1) : null;

            break;
          }

          case OpenFragmentTag: {
            m.advance(tag);

            s.node = m.node;
            break;
          }

          case OpenNodeTag: {
            s.depths.path++;
            m.advance(tag);

            // this is targeting a node which has not been branched
            // m.pathParent.node !== s.node (they are clones)
            // add(s.node, )

            // m.pathParent.add(m.path.node);

            s.node = m.node;

            m.parent.add(m.node);

            updateSpans(m, s.node, 'open');

            break;
          }

          case CloseNodeTag: {
            const { node } = s;

            s.node = m.parent.node;
            s.depths.path--;

            const ref = btree.getAt(-2, m.pathParent.node.children);

            if (ref.type === ReferenceTag && ref?.value.name === '@') {
              const cooked = node.flags.hasGap
                ? null
                : ctx.languages
                    .get(node.language)
                    .getCooked?.(NodeFacade.wrap(node, ctx, true), s.span.name, facades.get(ctx)) ||
                  null;

              bindAttribute(m, s, 'cooked', cooked);

              nodeStates.get(m.node).unboundAttributes.delete('cooked');

              yield* s.emit();
            }

            m.advance(tag);

            updateSpans(m, s.result.path.node, 'close');

            if (!m.parent) {
              if (!s.source.done) {
                throw new Error('Parser failed to consume input');
              }

              if (s.balanced.size) {
                throw new Error('Parser did not match all balanced nodes');
              }
            }

            break;
          }

          case LiteralTag: {
            const { value: pattern } = tag;

            let result;
            if (
              s.result.tag.type === OpenNodeTag &&
              s.result.tag.value.attributes.balancer &&
              s.balanced.value.attributes.balanced === pattern
            ) {
              result = s.match(pattern);
            } else {
              result = s.guardedMatch(pattern);
            }

            if (result instanceof Promise) {
              result = yield result;
            }

            if (result) {
              let sourceStep = s.source.advance(getSourceLength(result));

              if (sourceStep instanceof Promise) {
                sourceStep = yield sourceStep;
              }

              m.advance(tag);
            } else {
              throw new Error('Failed to advance literal');
            }
            break;
          }

          case GapTag: {
            if (s.source.value == null && !s.source.done) {
              if (s.source.holding) {
                s.source.unshift();
              } else {
                const sourceStep = s.source.advance(1);

                if (sourceStep instanceof Promise) {
                  yield sourceStep;
                }
              }

              m.advance(tag);
            } else {
              throw new Error('Failed to advance gap');
            }
            break;
          }

          case ShiftTag: {
            s.source.shift();
            m.advance(tag);
            break;
          }

          default:
            m.advance(tag);
        }

        if (tag.type !== ReferenceTag) {
          s.referenceTagPath = null;
        }

        if (s.depth === 0) {
          // fails to go from reference to open tag because path linkage doesn't exist yet
          //   just create the linkage at different times? (before/after for branching)
          //      yeh: no more if (s.depth === 0)
          yield* s.emit();
        }

        returnValue = tag;
        break;
      }

      case 'match': {
        let { arguments: { 0: pattern } = [] } = instr;

        let result = s.guardedMatch(pattern);

        if (result instanceof Promise) {
          result = yield result;
        }

        returnValue = result && NodeFacade.wrap(treeFromStreamSync(result), ctx, true);
        break;
      }

      case 'openSpan': {
        let { arguments: { 0: name } = [] } = instr;
        s.spans = s.spans.push({ guard: null, name, path: s.path, type: 'Instruction' });
        break;
      }

      case 'closeSpan': {
        if (s.spans.value.type !== 'Instruction') throw new Error();
        s.spans = s.spans.pop();
        break;
      }

      case 'startFrame': {
        const {
          arguments: {
            0: { value: matcher } = {},
            1: { value: effects } = {},
            2: { value: options = {} } = {},
          } = [],
        } = instr;

        const { unboundAttributes } = options;

        if (shouldBranch(effects)) {
          s = s.branch();
        }

        const parentMatch = m;

        if (!language) throw new Error('not initialized');

        m = parentMatch
          ? parentMatch.startFrame(s, reifyExpression(matcher), effects)
          : Match.from(ctx, language, s, reifyExpression(matcher));

        if (!m.isNode && options.unboundAttributes) throw new Error();

        nodeStates.set(m.node, {
          unboundAttributes: m.isNode
            ? new Set(unboundAttributes)
            : new Set(parentMatch ? nodeStates.get(parentMatch.node).unboundAttributes || [] : []),
        });

        ({ language } = m);

        if (parentMatch) {
          let previousIndex = [CloseNodeTag, NullTag, GapTag].includes(s.result.tag.type)
            ? btree.getSum(parentMatch.node.children) - 1
            : s.result.childrenIndex;

          m.rangePreviousIndex = previousIndex;
        }

        returnValue = facades.get(m);
        break;
      }

      case 'endFrame': {
        const finishedMatch = m;
        m = m.endFrame();

        if (!m) break;

        let rejected = false;

        if (finishedMatch.s !== m.s) {
          if (!isEmpty(allTagsFor(finishedMatch.range)) || finishedMatch.allowEmpty) {
            s = s.accept();
            finishedMatch.rangeFinalIndex = btree.getSum(m.node.children) - 1;
          } else {
            finishedMatch.rangePreviousIndex = null;
            s = s.reject();
            rejected = true;
          }
        } else {
          finishedMatch.rangeFinalIndex = btree.getSum(m.node.children) - 1;
        }

        if (!rejected) {
          yield* s.emit();
        }

        returnValue = facades.get(m);
        break;
      }

      case 'bindAttribute': {
        const { arguments: { 0: key, 1: value } = [] } = instr;

        bindAttribute(m, s, key, value);

        yield* s.emit();

        break;
      }

      case 'throw': {
        const finishedMatch = m;
        m = m.endFrame();

        if (!m) {
          returnValue = m;
          break;
        }

        if (finishedMatch.s !== m.s) {
          finishedMatch.rangePreviousIndex = null;
          s = s.reject();
        } else {
          finishedMatch.rangeFinalIndex = btree.getSum(m.node.children) - 1;
        }

        returnValue = facades.get(m);
        break;
      }

      case 'write': {
        const { arguments: { 0: text, 1: { value: writeOptions } = {} } = [] } = instr;

        if (options.emitEffects) {
          yield buildWriteEffect(text, writeOptions);
        }
        break;
      }

      case 'getState': {
        returnValue = facades.get(s);
        break;
      }

      default: {
        throw new Error(`Unexpected call of {type: ${formatType(verb)}}`);
      }
    }

    co.advance(returnValue);
  }

  return s.node;
}
