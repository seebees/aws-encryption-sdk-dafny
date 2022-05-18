namespace aws.cryptography.primitives

operation HMac {
  input: HMacInput,
  output: HMacOutput,
}

structure HMacInput {
  digestAlgorithm: DigestAlgorithm,
  message: Blob,
}

@aws.polymorph#positional
structure HMacOutput {
  digest: Blob
}
