namespace aws.cryptography.materialProviders

operation InitializeEncryptionMaterials {
  input: InitializeMaterialsInput,
  output: EncryptionMaterials,
}

operation InitializeDecryptionMaterials {
  input: InitializeMaterialsInput,
  output: DecryptionMaterials,
}

// The initilize input is the same
// for both Encryption and Dedryption materials.
// This is because they MUST match.
// The the Decryption materials did not
// have exactly the same encryptoion context, for example 
// then decryption should fail.
structure InitializeMaterialsInput {
  @required
  algorithmSuiteId: AlgorithmSuiteId,

  @required
  encryptionContext: EncryptionContext,

  @sensitive
  signingKey: Blob
}

operation ValidEncryptionMaterialsTransition {
  input: ValidEncryptionMaterialsTransitionInput,
  output: ValidTransition
}

operation ValidDecryptionMaterialsTransition {
  input: ValidDecryptionMaterialsTransitionInput,
  output: ValidTransition
}

structure ValidEncryptionMaterialsTransitionInput {
  start: EncryptionMaterials,
  stop: EncryptionMaterials,
}

structure ValidDecryptionMaterialsTransitionInput {
  start: DecryptionMaterials,
  stop: DecryptionMaterials,
}

@aws.polymorph#positional
structure ValidTransition {
  valid: Boolean
}
