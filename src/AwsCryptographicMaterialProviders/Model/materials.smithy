namespace aws.cryptography.materialProviders

@readonly
operation InitializeEncryptionMaterials {
  input: InitializeMaterialsInput,
  output: EncryptionMaterials,
}

@readonly
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

@readonly
operation ValidEncryptionMaterialsTransition {
  input: ValidEncryptionMaterialsTransitionInput,
  errors: [InvalidEncryptionMaterialsTransition]
}

@readonly
operation ValidDecryptionMaterialsTransition {
  input: ValidDecryptionMaterialsTransitionInput,
  errors: [InvalidDecryptionMaterialsTransition]
}

structure ValidEncryptionMaterialsTransitionInput {
  start: EncryptionMaterials,
  stop: EncryptionMaterials,
}

structure ValidDecryptionMaterialsTransitionInput {
  start: DecryptionMaterials,
  stop: DecryptionMaterials,
}

@error("client")
structure InvalidEncryptionMaterialsTransition {
  @required
  message: String,
}
@error("client")
structure InvalidDecryptionMaterialsTransition {
  @required
  message: String,
}
