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



	datatype Error =
		| AwsCryptographicPrimitivesError(message: string)
		| IncorrectLength()
		| Unknown(message: string)
		| Opaque(obj: object)
	type OpaqueError = e: Error | e.Opaque? witness *


 datatype AES_GCM = AES_GCM (
	nameonly keyLength: int32 ,
	nameonly tagLength: int32 ,
	nameonly ivLength: int32 )
 datatype AESDecryptInput = AESDecryptInput (
	nameonly encAlg: AES_GCM ,
	nameonly key: seq<uint8> ,
	nameonly cipherTxt: seq<uint8> ,
	nameonly authTag: seq<uint8> ,
	nameonly iv: seq<uint8> ,
	nameonly aad: seq<uint8> )
 datatype AESEncryptInput = AESEncryptInput (
	nameonly encAlg: AES_GCM ,
	nameonly iv: seq<uint8> ,
	nameonly key: seq<uint8> ,
	nameonly msg: seq<uint8> ,
	nameonly aad: seq<uint8> )
 datatype AESEncryptOutput = AESEncryptOutput (
	nameonly cipherText: seq<uint8> ,
	nameonly authTag: seq<uint8> )
 trait {:termination false} IAtomicPrimitives {
 predicate DigestCalledWith ( input: DigestInput ) {true}
 predicate DigestSucceededWith (  input: DigestInput , output: seq<uint8> ) {true}
 method Digest ( input: DigestInput ) returns  ( output: Result<seq<uint8>, Error> )
	ensures DigestCalledWith (  input )
	ensures output.Success? ==> DigestSucceededWith (  input , output.value )

 predicate HMacCalledWith ( input: HMacInput ) {true}
 predicate HMacSucceededWith (  input: HMacInput , output: seq<uint8> ) {true}
 method HMac ( input: HMacInput ) returns  ( output: Result<seq<uint8>, Error> )
	ensures HMacCalledWith (  input )
	ensures output.Success? ==> HMacSucceededWith (  input , output.value )

 predicate HkdfExpandCalledWith ( input: HkdfExpandInput ) {true}
 predicate HkdfExpandSucceededWith (  input: HkdfExpandInput , output: seq<uint8> ) {true}
 method HkdfExpand ( input: HkdfExpandInput ) returns  ( output: Result<seq<uint8>, Error> )
	ensures HkdfExpandCalledWith (  input )
	ensures output.Success? ==> HkdfExpandSucceededWith (  input , output.value )

 predicate HkdfExtractCalledWith ( input: HkdfExtractInput ) {true}
 predicate HkdfExtractSucceededWith (  input: HkdfExtractInput , output: seq<uint8> ) {true}
 method HkdfExtract ( input: HkdfExtractInput ) returns  ( output: Result<seq<uint8>, Error> )
	ensures HkdfExtractCalledWith (  input )
	ensures output.Success? ==> HkdfExtractSucceededWith (  input , output.value )

 predicate AESDecryptCalledWith ( input: AESDecryptInput ) {true}
 predicate AESDecryptSucceededWith (  input: AESDecryptInput , output: seq<uint8> ) {true}
 method AESDecrypt ( input: AESDecryptInput ) returns  ( output: Result<seq<uint8>, Error> )
	ensures AESDecryptCalledWith (  input )
	ensures output.Success? ==> AESDecryptSucceededWith (  input , output.value )

 predicate GenerateRandomBytesCalledWith ( input: GenerateRandomBytesInput ) {true}
 predicate GenerateRandomBytesSucceededWith (  input: GenerateRandomBytesInput , output: seq<uint8> ) {true}
 method GenerateRandomBytes ( input: GenerateRandomBytesInput ) returns  ( output: Result<seq<uint8>, Error> )
	ensures GenerateRandomBytesCalledWith (  input )
	ensures output.Success? ==> GenerateRandomBytesSucceededWith (  input , output.value )

 predicate HkdfCalledWith ( input: HkdfInput ) {true}
 predicate HkdfSucceededWith (  input: HkdfInput , output: seq<uint8> ) {true}
 method Hkdf ( input: HkdfInput ) returns  ( output: Result<seq<uint8>, Error> )
	ensures HkdfCalledWith (  input )
	ensures output.Success? ==> HkdfSucceededWith (  input , output.value )

 predicate AESEncryptCalledWith ( input: AESEncryptInput ) {true}
 predicate AESEncryptSucceededWith (  input: AESEncryptInput , output: AESEncryptOutput ) {true}
 method AESEncrypt ( input: AESEncryptInput ) returns  ( output: Result<AESEncryptOutput, Error> )
	ensures AESEncryptCalledWith (  input )
	ensures output.Success? ==> AESEncryptSucceededWith (  input , output.value )

}
 trait {:termination false} IAwsCryptographicPrimitivesClient {
 predicate CreateAtomicPrimitivesCalledWith ( input: AwsCryptographicPrimitivesVersion ) {true}
 predicate CreateAtomicPrimitivesSucceededWith (  input: AwsCryptographicPrimitivesVersion , output: IAtomicPrimitives ) {true}
 method CreateAtomicPrimitives ( input: AwsCryptographicPrimitivesVersion ) returns  ( output: Result<IAtomicPrimitives, Error> )
	ensures CreateAtomicPrimitivesCalledWith (  input )
	ensures output.Success? ==> CreateAtomicPrimitivesSucceededWith (  input , output.value )

}

 datatype AwsCryptographicPrimitivesVersion =
	| V20211101
 datatype DigestAlgorithm =
	| SHA_512
	| SHA_384
	| SHA_256
 datatype DigestInput = DigestInput (
	nameonly digestAlgorithm: DigestAlgorithm ,
	nameonly message: seq<uint8> )
 datatype GenerateRandomBytesInput = GenerateRandomBytesInput (
	nameonly length: int32 )
 datatype HkdfExpandInput = HkdfExpandInput (
	nameonly digestAlgorithm: DigestAlgorithm ,
	nameonly prk: seq<uint8> ,
	nameonly info: Option<seq<uint8>> ,
	nameonly expectedLength: int32 )
 datatype HkdfExtractInput = HkdfExtractInput (
	nameonly digest: DigestAlgorithm ,
	nameonly salt: Option<seq<uint8>> ,
	nameonly ikm: seq<uint8> )
 datatype HkdfInput = HkdfInput (
	nameonly digest: DigestAlgorithm ,
	nameonly salt: Option<seq<uint8>> ,
	nameonly ikm: seq<uint8> ,
	nameonly info: Option<seq<uint8>> ,
	nameonly expectedLength: int64 )
 datatype HMacInput = HMacInput (
	nameonly digestAlgorithm: DigestAlgorithm,
	nameonly message: seq<uint8> )
}
