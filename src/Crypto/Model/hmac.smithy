namespace aws.cryptography.primitives

operation HMac {
  input: HMacInput,
  output: HMacOutput,
}

structure HMacInput {
  @required
  digestAlgorithm: DigestAlgorithm,
  @required
  message: Blob,
}

@aws.polymorph#positional
structure HMacOutput {
  digest: Blob
}
