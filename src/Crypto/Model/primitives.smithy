namespace aws.cryptography.primitives

@range(min: 0)
integer PositiveInteger

@aws.polymorph#localService(
  sdkId: "Crypto",
  config: CryptoConfig,
)
service AwsCryptographicPrimitives {
  version: "2020-10-24",
  operations: [
    GenerateRandomBytes,
    Digest,
    HMac,
    HkdfExtract,
    HkdfExpand,
    Hkdf,
    AESEncrypt,
    AESDecrypt,
  ]
}

structure CryptoConfig {}

///////////////////
// Errors

@error("client")
structure AwsCryptographicPrimitivesError {
  @required
  message: String,
}
