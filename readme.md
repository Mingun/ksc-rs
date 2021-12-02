
Differences from [original]
===========================
When feature `compatible` is not enabled (default), the following differences are present:

- `repeat-until: <falsy value>` is forbidden. Such value leads to an infinity parse
  cycle, so it is useless to allow it
- `repeat-expr: <non-positive value>` is forbidden. Such values has no meaning

[original]: https://github.com/kaitai-io/kaitai_struct_compiler
