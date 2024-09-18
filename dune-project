(lang dune 3.11)
(using coq 0.2)
(using mdx 0.2)
(name Wasm)
(version 2.0)

(generate_opam_files true)
(license MIT)
(source (github logsem/iris-wasmfx))

(package
  (name Wasm)
  (synopsis "WasmFX formalisation in Coq")
  (description "WasmFX formalisation in Coq, following the AFP formalisation of Conrad Watt"))



(warnings (deprecated_coq_lang_lt_08 disabled))
