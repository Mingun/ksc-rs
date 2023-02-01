meta:
  id: builtin
  endian: be
  encoding: utf-8
seq:
  - id: bytes
    size: unknown
  - id: unsigned
    type: unsigned
    size: 20
  - id: signed
    type: signed
instances:
  parse:
    pos: 10
    type: str
    terminator: 0x10
  value:
    value: unsigned
  type:
    type: signed
types:
  unsigned:
    meta:
      endian:
        switch-on: 1 == 2
        cases:
          true: be
          _: le
    seq:
      - id: u1
        type: u1

      - id: u2
        type: u2
      - id: u2be
        type: u2be
      - id: u2le
        type: u2le

      - id: u4
        type: u4
      - id: u4be
        type: u4be
      - id: u4le
        type: u4le

      - id: u8
        type: u8
      - id: u8be
        type: u8be
      - id: u8le
        type: u8le
  signed:
    seq:
      - id: s1
        type: s1

      - id: s2
        type: s2
      - id: s2be
        type: s2be
      - id: s2le
        type: s2le

      - id: s4
        type: s4
      - id: s4be
        type: s4be
      - id: s4le
        type: s4le

      - id: s8
        type: s8
      - id: s8be
        type: s8be
      - id: s8le
        type: s8le
  switch:
    seq:
      - id: a
        type: u1
      - id: b
        type: u1
      - id: c
        type: u1
      - id: switch
        type:
          switch-on: 4 - 2
          cases:
            0: u1
            1: u2be
            2: u4be
            _: u8be
      - id: if
        type:
          switch-on: 4 - 2
          cases:
            a: u1
            b: u2be
            c: u4be
            _: u8be
  quantity:
    seq:
      - id: field
        type: u1
      - type: u1
      - id: condition
        type: u1
        if: true
      - id: repeat_eos
        type: u1
        repeat: eos
      - id: repeat_expr
        type: u1
        repeat: expr
        repeat-expr: 2
      - id: repeat_until
        type: u1
        repeat: until
        repeat-until: false
      - id: condition_array
        type: u1
        repeat: expr
        repeat-expr: 2
        if: true
  size:
    seq:
      - id: size
        type: switch
        size: 10
      - id: eos
        type: switch
        size-eos: true
      - id: terminator
        type: switch
        terminator: 0xFF
      - id: size_terminator
        type: switch
        size: 10
        terminator: 0
      - id: eos_terminator
        type: switch
        size-eos: true
        terminator: 0
  types:
    seq:
      - id: f4
        type: f4
      - id: f4be
        type: f4be
      - id: f4le
        type: f4le
      - id: f8
        type: f8
      - id: f8be
        type: f8be
      - id: f8le
        type: f8le
      - id: str
        type: str
        size-eos: true
      - id: strz
        type: strz
      - id: bytes
        size-eos: true
      - id: bytes_terminator
        terminator: 0
      - id: bytes_eos_terminator
        size-eos: true
        terminator: 0
  enums:
    seq:
      - id: enum
        type: u1
        enum: enum
  # Для тестов разрешения коллизии имен
  names:
    seq:
      - size: 1
      - size: 1
      - id: unnamed0
        size: 1
      - id: unnamed01
        size: 1
      - id: unnamed0_1
        size: 1
      - id: enum
        size: 1
      - id: enum1
        size: 1
      - id: enum1_1
        size: 1
  int_properties:
    seq:
      - id: u1_number
        type: u1
      - id: u2_number
        type: u2
      - id: u4_number
        type: u4
      - id: u8_number
        type: u8

      - id: s1_number
        type: s1
      - id: s2_number
        type: s2
      - id: s4_number
        type: s4
      - id: s8_number
        type: s8
    instances:
      u1_to_s:
        value: u1_number.to_s
      u2_to_s:
        value: u2_number.to_s
      u4_to_s:
        value: u4_number.to_s
      u8_to_s:
        value: u8_number.to_s

      s1_to_s:
        value: s1_number.to_s
      s2_to_s:
        value: s2_number.to_s
      s4_to_s:
        value: s4_number.to_s
      s8_to_s:
        value: s8_number.to_s
  float_properties:
    seq:
      - id: f4_number
        type: f4
      - id: f8_number
        type: f8
    instances:
      f4_to_i:
        value: f4_number.to_i
      f8_to_i:
        value: f8_number.to_i
  array_properties:
    seq:
      - id: array
        size: 20
    instances:
      to_s:
        value: array.to_s("utf-8")
      length:
        value: array.length
      first:
        value: array.first
      last:
        value: array.last
      size:
        value: array.size
      min:
        value: array.min
      max:
        value: array.max
  string_properties:
    seq:
      - id: string
        type: strz
    instances:
      length:
        value: string.length
      reverse:
        value: string.reverse
      substring:
        value: string.substring(0, 2)
      to_i:
        value: string.to_i
      to_i_16:
        value: string.to_i(16)
  bool_properties:
    seq:
      - id: bool
        type: b1
    instances:
      to_i:
        value: bool.to_i
  enum_properties:
    seq:
      - id: enum
        type: u1
        enum: enum
    instances:
      to_i:
        value: enum.to_i
  stream_properties:
    instances:
      eof:
        value: _io.eof
      size:
        value: _io.size
      pos:
        value: _io.pos
  user_type_properties:
    seq:
      - id: user_type
        type: size
    instances:
      root:
        value: user_type._root
      # parent: # Ошибка: Unable to derive _parent type in builtin::size
      #   value: user_type._parent
      io:
        value: user_type._io

enums:
  enum:
    0: e0
    1: e1
