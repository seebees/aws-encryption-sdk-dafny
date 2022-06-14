// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/StandardLibrary.dfy"
 include "../../Util/UTF8.dfy"
 module AwsCryptographyPrimitivesTypes
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
 // Predicates are separated from the trait. This is temporary.
 predicate {:opaque} GenerateRandomBytesCalledWith ( input: GenerateRandomBytesInput ) {true}
 predicate {:opaque} GenerateRandomBytesSucceededWith (  input: GenerateRandomBytesInput , output: seq<uint8> ) {true}
 predicate {:opaque} DigestCalledWith ( input: DigestInput ) {true}
 predicate {:opaque} DigestSucceededWith (  input: DigestInput , output: seq<uint8> ) {true}
 predicate {:opaque} HMacCalledWith ( input: HMacInput ) {true}
 predicate {:opaque} HMacSucceededWith (  input: HMacInput , output: seq<uint8> ) {true}
 predicate {:opaque} HkdfExtractCalledWith ( input: HkdfExtractInput ) {true}
 predicate {:opaque} HkdfExtractSucceededWith (  input: HkdfExtractInput , output: seq<uint8> ) {true}
 predicate {:opaque} HkdfExpandCalledWith ( input: HkdfExpandInput ) {true}
 predicate {:opaque} HkdfExpandSucceededWith (  input: HkdfExpandInput , output: seq<uint8> ) {true}
 predicate {:opaque} HkdfCalledWith ( input: HkdfInput ) {true}
 predicate {:opaque} HkdfSucceededWith (  input: HkdfInput , output: seq<uint8> ) {true}
 predicate {:opaque} AESEncryptCalledWith ( input: AESEncryptInput ) {true}
 predicate {:opaque} AESEncryptSucceededWith (  input: AESEncryptInput , output: AESEncryptOutput ) {true}
 predicate {:opaque} AESDecryptCalledWith ( input: AESDecryptInput ) {true}
 predicate {:opaque} AESDecryptSucceededWith (  input: AESDecryptInput , output: seq<uint8> ) {true}
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
 nameonly length: int32
 )
 datatype HkdfExpandInput = | HkdfExpandInput (
 nameonly digestAlgorithm: DigestAlgorithm ,
 nameonly prk: seq<uint8> ,
 nameonly info: Option<seq<uint8>> ,
 nameonly expectedLength: int32
 )
 datatype HkdfExtractInput = | HkdfExtractInput (
 nameonly digest: DigestAlgorithm ,
 nameonly salt: Option<seq<uint8>> ,
 nameonly ikm: seq<uint8>
 )
 datatype HkdfInput = | HkdfInput (
 nameonly digest: DigestAlgorithm ,
 nameonly salt: Option<seq<uint8>> ,
 nameonly ikm: seq<uint8> ,
 nameonly info: Option<seq<uint8>> ,
 nameonly expectedLength: int64
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
