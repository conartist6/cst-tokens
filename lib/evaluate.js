import { Coroutine } from '@bablr/coroutine';
import { buildCall, buildWriteEffect } from '@bablr/agast-helpers/builders';
import { getStreamIterator, isEmpty, StreamIterable } from '@bablr/agast-helpers/stream';
import { formatType } from './utils/format.js';
import { facades } from './facades.js';
import { State } from './state.js';
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
} from '@bablr/agast-helpers/symbols';
import { NodeFacade } from './node.js';
import { treeFromStreamSync } from '@bablr/agast-helpers/tree';
import * as btree from '@bablr/agast-helpers/btree';
import { getEmbeddedTag } from '@bablr/agast-vm-helpers/deembed';
import { buildIdentifier, buildTuple, buildTupleValues } from '@bablr/agast-vm-helpers/builders';
import { Match } from './match.js';
import { reifyExpression, shouldBranch } from '@bablr/agast-vm-helpers';
import { allTagsFor, TagPath } from '@bablr/agast-helpers/path';

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
      case 'advance': {
        const { arguments: { 0: embeddedTags } = [] } = instr;

        const tag = getEmbeddedTag(embeddedTags);

        switch (tag.type) {
          case DoctypeTag: {
            m = Match.from(
              ctx,
              ctx.languages.get(tag.value.attributes['bablr-language']),
              s,
              null,

              options,
            );

            m.advance(tag);
            break;
          }

          case ReferenceTag: {
            m.advance(tag);

            s.referenceTagPath = m.parent ? TagPath.from(m.path, -1) : null;

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

            updateSpans(s, s.node, 'open');

            break;
          }

          case CloseNodeTag: {
            const { node } = s;

            s.node = m.parent.node;
            s.depths.path--;

            if (m.path.reference?.value.name === '@') {
              const cooked = node.flags.hasGap
                ? null
                : ctx.languages
                    .get(node.language)
                    .getCooked?.(NodeFacade.wrap(node, ctx, true), s.span.name, facades.get(ctx)) ||
                  null;

              yield buildCall(
                buildIdentifier('bindAttribute'),
                buildTuple(buildTupleValues(['cooked', cooked])),
              );
            }

            m.advance(tag);

            updateSpans(s, s.result.path.node, 'close');

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
            2: { value: options } = {},
          } = [],
        } = instr;

        if (shouldBranch(effects)) {
          s = s.branch();
        }

        const parentMatch = m;

        m = m.startFrame(s, reifyExpression(matcher), effects, options);

        if (m.isNode && !shouldBranch(effects)) {
          // Adding to the old node!
          // m.node never gets updated on s.branch()
          parentMatch.add(m.node);
        }

        m.rangePreviousIndex = s.result.childrenIndex;

        returnValue = facades.get(m);
        break;
      }

      case 'endFrame': {
        const finishedMatch = m;
        m = m.endFrame();

        // circular dep
        //   isEmpty always true because we haven't done add() yet
        //     to know if we should do add() we must know isEmpty
        //     we need initialRange!
        let rejected = false;

        if (finishedMatch.s !== m.s) {
          if (
            (finishedMatch.range && !isEmpty(allTagsFor(finishedMatch.range))) ||
            finishedMatch.allowEmpty
          ) {
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
          if (finishedMatch.isNode && shouldBranch(finishedMatch.effects)) {
            m.add(finishedMatch.node);
          }

          if (s.depth === 0) {
            yield* s.emit();
          }
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
