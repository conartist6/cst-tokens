import { ReferenceTag } from '@bablr/agast-helpers/symbols';
import { getOpenTag } from '@bablr/agast-helpers/tree';

export function updateSpans(s, node, phase) {
  const { path } = s;
  const { flags, attributes } = node;
  const ref = path.reference;

  const openTag = getOpenTag(node);

  const intrinsic = ref.type === ReferenceTag && !ref.value.hasGap;

  switch (phase) {
    case 'open': {
      const { balancedSpan, span: innerSpan, balanced, balancer, openSpan } = attributes || {};

      if (!intrinsic && (balancer || balanced)) {
        throw new Error('balanced tokens must be instrinsic');
      }

      if (balancedSpan && !balanced) throw new Error();

      if (openSpan) {
        s.spans = s.spans.push({
          type: 'Explicit',
          name: openSpan,
          path: s.path,
          guard: null,
        });
      }

      if (balancer) {
        const balancedNode = s.balanced.value;

        if (!s.balanced.size) throw new Error();

        if (!balancedNode.attributes.balanced) {
          throw new Error();
        }

        s.balanced = s.balanced.pop();

        s.spans = s.spans.pop();
      }

      if (innerSpan) {
        s.spans = s.spans.push({
          type: 'Inner',
          name: innerSpan,
          path: s.path,
          guard: null,
        });
      }

      break;
    }

    case 'close': {
      const { balancedSpan, span: innerSpan, closeSpan, balanced } = attributes || {};

      if (balanced) {
        s.balanced = s.balanced.push(node);

        s.spans = s.spans.push({
          type: 'Lexical',
          name: balancedSpan || s.span.name,
          path: s.path,
          guard: balanced === true ? null : balanced,
        });
      }

      if (closeSpan) {
        if (s.spans.value.type !== 'Explicit') throw new Error();
        s.spans = s.spans.pop();
      }

      if (innerSpan) {
        s.spans = s.spans.pop();
      }
      break;
    }
    default:
      throw new Error();
  }
}
