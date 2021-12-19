
Differences from [original]
===========================
When feature `compatible` is not enabled (default), the following differences are present:

- `repeat-until: <falsy value>` is forbidden. Such value leads to an infinity parse
  cycle, so it is useless to allow it
- `repeat-expr: <non-positive value>` is forbidden. Such values has no meaning
- `repeat` key is optional if `repeat-expr` or `repeat-until` is defined ([#776])

[original]: https://github.com/kaitai-io/kaitai_struct_compiler
[#776]: https://github.com/kaitai-io/kaitai_struct/issues/776
