namespace aws.cryptography.materialProviders

structure AlgorithmSuiteInfo {
  @required
  id: AlgorithmSuiteId,
  @required
  encrypt: aws.cryptography.primitives#AES_GCM,
  @required
  kdf: DerivationAlgorithm,
  @required
  commitment: DerivationAlgorithm,
  @required
  signature: SignatureAlgorithm,
}

union DerivationAlgorithm {
  HKDF: HKDF,
  IDENTITY: IDENTITY,
  None: None,
}

union SignatureAlgorithm {
  ECDSA: ECDSA,
  None: None
}

structure HKDF {
  @required
  hmac: aws.cryptography.primitives#DigestAlgorithm,
  @required
  saltLength: aws.cryptography.primitives#PositiveInteger,
  @required
  inputKeyLength: aws.cryptography.primitives#PositiveInteger,
  @required
  outputKeyLength: aws.cryptography.primitives#PositiveInteger,
}
structure IDENTITY {}
structure None {}

structure ECDSA {
  @required
  curve: String
}
