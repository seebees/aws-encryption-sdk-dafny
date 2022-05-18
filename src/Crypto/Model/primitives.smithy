namespace aws.cryptography.primitives

// use aws.polymorph#reference
// use aws.polymorph#positional

@enum([
    {
        name: "V20211101",
        value: "V20211101",
    },
])
string AwsCryptographicPrimitivesVersion

service AwsCryptographicPrimitives {
  version: AwsCryptographicPrimitivesVersion,
  operations: [CreateAtomicPrimitives],
}

operation CreateAtomicPrimitives {
  input: CreateAtomicPrimitivesInput,
  output: AtomicPrimitivesReference,
  errors: [AwsCryptographicPrimitivesError],
}

@aws.polymorph#positional
structure CreateAtomicPrimitivesInput {
  version: AwsCryptographicPrimitivesVersion
}

@aws.polymorph#reference(resource: AtomicPrimitives)
structure AtomicPrimitivesReference {}

/////////////
// AtomicPrimitives
resource AtomicPrimitives {
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


///////////////////
// Errors

@error("client")
structure AwsCryptographicPrimitivesError {
  @required
  message: String,
}
