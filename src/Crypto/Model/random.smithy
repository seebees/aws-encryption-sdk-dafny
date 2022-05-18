namespace aws.cryptography.primitives

operation GenerateRandomBytes {
  input: GenerateRandomBytesInput,
  output: GenerateRandomBytesOutput,
  errors: []
}

structure GenerateRandomBytesInput {
  @required
  length: Long
}

@aws.polymorph#positional
structure GenerateRandomBytesOutput {
  data: Blob
}
