namespace aws.cryptography.primitives

operation HkdfExtract {
  input: HkdfExtractInput,
  output: HkdfExtractOutput,
}
operation HkdfExpand {
  input: HkdfExpandInput,
  output: HkdfExpandOutput,
}
operation Hkdf {
  input: HkdfInput,
  output: HkdfOutput,
}

structure HkdfExtractInput {
  @required
  digest: DigestAlgorithm,
  salt: Blob,
  @required
  ikm: Blob,
}

@aws.polymorph#positional
structure HkdfExtractOutput {
  prk: Blob
}

structure HkdfExpandInput {
  @required
  digestAlgorithm: DigestAlgorithm,
  @required
  prk: Blob,
  info: Blob,
  @required
  expectedLength: Integer
}

@aws.polymorph#positional
structure HkdfExpandOutput {
  okm: Blob,
}

structure HkdfInput {
  @required
  digest: DigestAlgorithm,
  salt: Blob,
  @required
  ikm: Blob,
  info: Blob,
  @required
  expectedLength: Long
}

@aws.polymorph#positional
structure HkdfOutput {
  okm: Blob,
}