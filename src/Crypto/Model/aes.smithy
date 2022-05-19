namespace aws.cryptography.primitives

operation AESEncrypt {
  input: AESEncryptInput,
  output: AESEncryptOutput,
  errors: []
}
operation AESDecrypt {
  input: AESDecryptInput,
  output: AESDecryptOutput,
  errors: []
}

structure AESEncryptInput {
  @required
  encAlg: AES_GCM,
  @required
  iv: Blob,
  @required
  key: Blob,
  @required
  msg: Blob,
  @required
  aad: Blob
}

structure AESEncryptOutput {
  @required
  cipherText: Blob,
  @required
  authTag: Blob
}

structure AESDecryptInput {
  @required
  encAlg: AES_GCM,
  @required
  key: Blob,
  @required
  cipherTxt: Blob,
  @required
  authTag: Blob,
  @required
  iv: Blob,
  @required
  aad: Blob
}

@aws.polymorph#positional
structure AESDecryptOutput {
  plaintext: Blob
}

structure AES_GCM {
  @required
  keyLength: Integer,
  @required
  tagLength: Integer,
  @required
  ivLength: Integer
}
