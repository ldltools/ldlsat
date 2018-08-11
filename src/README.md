# Programs

- ldl2mso  
  usage: ldl2mso _infile_

- ldl2re  
  usage: ldl2re [-p] [-t _fmt_] _infile_
  - _infile_ can be formatted in _ldl_ or _json_ (auto-recognized)
  - -t _fmt_: specifies the output format.
    _fmt_ can be either of _json_ (default) and _caml_, and _re_

- ldl2afw  
  usage: ldl2afw [-p] [-t _fmt_] _infile_   
  - _infile_ can be formatted in _ldl_ or _json_ (auto-recognized)
  - -t _fmt_: specifies the output format.
    _fmt_ can be either of _json_ (default) and _caml_

- ldlsimp  
  usage: ldlsimp [--tac _tac_,_tac_,..] _infile_

## source/intermediate languages

### LDL
- its grammar is defined in [ldl\_p.mly](ldl_p.mly)
- its abstract syntax is defined in [ldl.mli](src/ldl.mli)
- __ldl2re__ tranforms _ldl_ to _re_

### RE
- its abstract syntax is defined in [re.mli](re.mli)
- __re2mso__ tranforms _re_ to _mso_

### MSO
- its abstract grammar is defined in [mso/mso.mli](mso/mso.mli)
- __mso2dfa__ tranforms _mso_ to _dfa_ (by internally using __mona__)
