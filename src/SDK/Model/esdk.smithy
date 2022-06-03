namespace aws.encryptionSdk

use aws.cryptography.materialProviders#KeyringReference
use aws.cryptography.materialProviders#CryptographicMaterialsManagerReference
use aws.cryptography.materialProviders#EncryptionContext
use aws.cryptography.materialProviders#AlgorithmSuiteId
use aws.cryptography.materialProviders#CommitmentPolicy
use aws.polymorph#reference

/////////////
// ESDK Client Creation

// TODO add a trait to indicate that 'Client' should not be appended to this name,
// and that the code gen should expose operations under this service statically if
// possible in the target language
@aws.polymorph#localService(
  sdkId: "ESDK",
  config: AwsEncryptionSdkConfig,
)
service AwsEncryptionSdk {
  version: "2020-10-24",
  operations: [Encrypt, Decrypt],
  errors: [AwsEncryptionSdkException],
}

@range(min: 1)
long CountingNumbers

structure AwsEncryptionSdkConfig {
  commitmentPolicy: CommitmentPolicy,
  maxEncryptedDataKeys: CountingNumbers,
}

/////////////
// ESDK Operations

operation Encrypt {
  input: EncryptInput,
  output: EncryptOutput,
}

structure EncryptInput {
  @required
  plaintext: Blob,

  encryptionContext: EncryptionContext,

  // One of keyring or CMM are required
  materialsManager: CryptographicMaterialsManagerReference,
  keyring: KeyringReference,

  algorithmSuiteId: AlgorithmSuiteId,

  frameLength: Long
}

structure EncryptOutput {
  @required
  ciphertext: Blob,

  @required
  encryptionContext: EncryptionContext,

  @required
  algorithmSuiteId: AlgorithmSuiteId,
}

operation Decrypt {
  input: DecryptInput,
  output: DecryptOutput,
  errors: [AwsEncryptionSdkException],
}

structure DecryptInput {
  @required
  ciphertext: Blob,

  // One of keyring or CMM are required
  materialsManager: CryptographicMaterialsManagerReference,
  keyring: KeyringReference,
}

structure DecryptOutput {
  @required
  plaintext: Blob,

  @required
  encryptionContext: EncryptionContext,

  @required
  algorithmSuiteId: AlgorithmSuiteId,

  // The spec says that decrypt SHOULD also return the parsed
  // header. We're omitting this for now, until we can spend
  // some more time figuring out what it looks like to model
  // the message format and message header in Smithy.
}

/////////////
// Errors

@error("client")
structure AwsEncryptionSdkException {
  @required
  message: String,
}
