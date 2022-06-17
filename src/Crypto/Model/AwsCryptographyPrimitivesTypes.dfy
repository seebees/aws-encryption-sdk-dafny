// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/StandardLibrary.dfy"
 include "../../Util/UTF8.dfy"
 module {:extern "Dafny.Aws.Cryptography.Primitives.Types" } AwsCryptographyPrimitivesTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 datatype AES_GCM = | AES_GCM (
 nameonly keyLength: int32 ,
 nameonly tagLength: int32 ,
 nameonly ivLength: int32
 )
 datatype AESDecryptInput = | AESDecryptInput (
 nameonly encAlg: AES_GCM ,
 nameonly key: seq<uint8> ,
 nameonly cipherTxt: seq<uint8> ,
 nameonly authTag: seq<uint8> ,
 nameonly iv: seq<uint8> ,
 nameonly aad: seq<uint8>
 )
 datatype AESEncryptInput = | AESEncryptInput (
 nameonly encAlg: AES_GCM ,
 nameonly iv: seq<uint8> ,
 nameonly key: seq<uint8> ,
 nameonly msg: seq<uint8> ,
 nameonly aad: seq<uint8>
 )
 datatype AESEncryptOutput = | AESEncryptOutput (
 nameonly cipherText: seq<uint8> ,
 nameonly authTag: seq<uint8>
 )
 trait {:termination false} IAwsCryptographicPrimitivesClient
 {
 method  GenerateRandomBytes
 ( input: GenerateRandomBytesInput )
 returns (output: Result<seq<uint8>, Error>)
  ensures GenerateRandomBytesCalledWith (  input )
 ensures output.Success? ==> GenerateRandomBytesSucceededWith (  input , output.value )
 method  Digest
 ( input: DigestInput )
 returns (output: Result<seq<uint8>, Error>)
  ensures DigestCalledWith (  input )
 ensures output.Success? ==> DigestSucceededWith (  input , output.value )
 method  HMac
 ( input: HMacInput )
 returns (output: Result<seq<uint8>, Error>)
  ensures HMacCalledWith (  input )
 ensures output.Success? ==> HMacSucceededWith (  input , output.value )
 method  HkdfExtract
 ( input: HkdfExtractInput )
 returns (output: Result<seq<uint8>, Error>)
  ensures HkdfExtractCalledWith (  input )
 ensures output.Success? ==> HkdfExtractSucceededWith (  input , output.value )
 method  HkdfExpand
 ( input: HkdfExpandInput )
 returns (output: Result<seq<uint8>, Error>)
  ensures HkdfExpandCalledWith (  input )
 ensures output.Success? ==> HkdfExpandSucceededWith (  input , output.value )
 method  Hkdf
 ( input: HkdfInput )
 returns (output: Result<seq<uint8>, Error>)
  ensures HkdfCalledWith (  input )
 ensures output.Success? ==> HkdfSucceededWith (  input , output.value )
 method  AESEncrypt
 ( input: AESEncryptInput )
 returns (output: Result<AESEncryptOutput, Error>)
  ensures AESEncryptCalledWith (  input )
 ensures output.Success? ==> AESEncryptSucceededWith (  input , output.value )
 method  AESDecrypt
 ( input: AESDecryptInput )
 returns (output: Result<seq<uint8>, Error>)
  ensures AESDecryptCalledWith (  input )
 ensures output.Success? ==> AESDecryptSucceededWith (  input , output.value )
}
 // Predicates are separated from the trait.
 // This is intentional, otherwise they would need to be reDefined in the concrete class.
 // In the concrete method you MUST use `assume` for the `ensures` clause to verify.
 // However you MUST NOT use `assume` anywhere else.
 // Otherwise any such proof will be unsound.
 predicate {:axiom} GenerateRandomBytesCalledWith ( input: GenerateRandomBytesInput )
 lemma {:axiom} AssumeGenerateRandomBytesCalledWith ( input: GenerateRandomBytesInput )
 ensures GenerateRandomBytesCalledWith ( input )
 predicate {:axiom} GenerateRandomBytesSucceededWith ( input: GenerateRandomBytesInput , output: seq<uint8> )
 lemma {:axiom} AssumeGenerateRandomBytesSucceededWith ( input: GenerateRandomBytesInput , output: seq<uint8> )
 ensures GenerateRandomBytesSucceededWith ( input , output )
 predicate {:axiom} DigestCalledWith ( input: DigestInput )
 lemma {:axiom} AssumeDigestCalledWith ( input: DigestInput )
 ensures DigestCalledWith ( input )
 predicate {:axiom} DigestSucceededWith ( input: DigestInput , output: seq<uint8> )
 lemma {:axiom} AssumeDigestSucceededWith ( input: DigestInput , output: seq<uint8> )
 ensures DigestSucceededWith ( input , output )
 predicate {:axiom} HMacCalledWith ( input: HMacInput )
 lemma {:axiom} AssumeHMacCalledWith ( input: HMacInput )
 ensures HMacCalledWith ( input )
 predicate {:axiom} HMacSucceededWith ( input: HMacInput , output: seq<uint8> )
 lemma {:axiom} AssumeHMacSucceededWith ( input: HMacInput , output: seq<uint8> )
 ensures HMacSucceededWith ( input , output )
 predicate {:axiom} HkdfExtractCalledWith ( input: HkdfExtractInput )
 lemma {:axiom} AssumeHkdfExtractCalledWith ( input: HkdfExtractInput )
 ensures HkdfExtractCalledWith ( input )
 predicate {:axiom} HkdfExtractSucceededWith ( input: HkdfExtractInput , output: seq<uint8> )
 lemma {:axiom} AssumeHkdfExtractSucceededWith ( input: HkdfExtractInput , output: seq<uint8> )
 ensures HkdfExtractSucceededWith ( input , output )
 predicate {:axiom} HkdfExpandCalledWith ( input: HkdfExpandInput )
 lemma {:axiom} AssumeHkdfExpandCalledWith ( input: HkdfExpandInput )
 ensures HkdfExpandCalledWith ( input )
 predicate {:axiom} HkdfExpandSucceededWith ( input: HkdfExpandInput , output: seq<uint8> )
 lemma {:axiom} AssumeHkdfExpandSucceededWith ( input: HkdfExpandInput , output: seq<uint8> )
 ensures HkdfExpandSucceededWith ( input , output )
 predicate {:axiom} HkdfCalledWith ( input: HkdfInput )
 lemma {:axiom} AssumeHkdfCalledWith ( input: HkdfInput )
 ensures HkdfCalledWith ( input )
 predicate {:axiom} HkdfSucceededWith ( input: HkdfInput , output: seq<uint8> )
 lemma {:axiom} AssumeHkdfSucceededWith ( input: HkdfInput , output: seq<uint8> )
 ensures HkdfSucceededWith ( input , output )
 predicate {:axiom} AESEncryptCalledWith ( input: AESEncryptInput )
 lemma {:axiom} AssumeAESEncryptCalledWith ( input: AESEncryptInput )
 ensures AESEncryptCalledWith ( input )
 predicate {:axiom} AESEncryptSucceededWith ( input: AESEncryptInput , output: AESEncryptOutput )
 lemma {:axiom} AssumeAESEncryptSucceededWith ( input: AESEncryptInput , output: AESEncryptOutput )
 ensures AESEncryptSucceededWith ( input , output )
 predicate {:axiom} AESDecryptCalledWith ( input: AESDecryptInput )
 lemma {:axiom} AssumeAESDecryptCalledWith ( input: AESDecryptInput )
 ensures AESDecryptCalledWith ( input )
 predicate {:axiom} AESDecryptSucceededWith ( input: AESDecryptInput , output: seq<uint8> )
 lemma {:axiom} AssumeAESDecryptSucceededWith ( input: AESDecryptInput , output: seq<uint8> )
 ensures AESDecryptSucceededWith ( input , output )
 datatype CryptoConfig = | CryptoConfig (
 
 )
 datatype DigestAlgorithm =
	| SHA_512
	| SHA_384
	| SHA_256
 datatype DigestInput = | DigestInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly message: seq<uint8>
 )
 datatype GenerateRandomBytesInput = | GenerateRandomBytesInput (
 nameonly length: PositiveInteger
 )
 datatype HkdfExpandInput = | HkdfExpandInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly prk: seq<uint8> ,
 nameonly info: seq<uint8> ,
 nameonly expectedLength: PositiveInteger
 )
 datatype HkdfExtractInput = | HkdfExtractInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly salt: Option<seq<uint8>> ,
 nameonly ikm: seq<uint8>
 )
 datatype HkdfInput = | HkdfInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly salt: Option<seq<uint8>> ,
 nameonly ikm: seq<uint8> ,
 nameonly info: seq<uint8> ,
 nameonly expectedLength: PositiveInteger
 )
 datatype HMacInput = | HMacInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly key: seq<uint8> ,
 nameonly message: seq<uint8>
 )
 type PositiveInteger = x: int32 | IsValid_PositiveInteger(x) witness *
 predicate method IsValid_PositiveInteger(x: int32) {
 ( 0 <= x  )
}
 datatype Error =
 // Local Error structures are listed here
 | AwsCryptographicPrimitivesError (
 nameonly message: string
 )
 // Any dependent models are listed here
 
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AwsCryptographyPrimitivesAbstract
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = AwsCryptographyPrimitivesTypes
 function method DefaultCryptoConfig(): CryptoConfig
 method Crypto(config: CryptoConfig := DefaultCryptoConfig())
 returns (res: Result<IAwsCryptographicPrimitivesClient, Error>)
}
