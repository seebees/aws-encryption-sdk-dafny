// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/StandardLibrary.dfy"
 include "../../Util/UTF8.dfy"
 abstract module Aws.Cryptography.PrimitivesAbstract
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 datatype AES_GCM = AES_GCM (
	nameonly keyLength: int64 ,
	nameonly tagLength: int64 ,
	nameonly ivLength: int64 )
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
	nameonly cipherText: Option<seq<uint8>> ,
	nameonly authTag: Option<seq<uint8>> )
 trait {:termination false} IAtomicPrimitives {
 predicate {:opaque} DigestCalledWith ( input: DigestInput ) {true}
 predicate {:opaque} DigestSucceededWith (  input: DigestInput , output: seq<uint8> ) {true}
 method Digest ( input: DigestInput ) returns  ( output: Result<seq<uint8>, IAwsCryptographicPrimitivesException> )
	ensures DigestCalledWith (  input )
	ensures output.Success? ==> DigestSucceededWith (  input , output.value )

 predicate {:opaque} HMacCalledWith ( input: HMacInput ) {true}
 predicate {:opaque} HMacSucceededWith (  input: HMacInput , output: seq<uint8> ) {true}
 method HMac ( input: HMacInput ) returns  ( output: Result<seq<uint8>, IAwsCryptographicPrimitivesException> )
	ensures HMacCalledWith (  input )
	ensures output.Success? ==> HMacSucceededWith (  input , output.value )

 predicate {:opaque} HkdfExpandCalledWith ( input: HkdfExpandInput ) {true}
 predicate {:opaque} HkdfExpandSucceededWith (  input: HkdfExpandInput , output: seq<uint8> ) {true}
 method HkdfExpand ( input: HkdfExpandInput ) returns  ( output: Result<seq<uint8>, IAwsCryptographicPrimitivesException> )
	ensures HkdfExpandCalledWith (  input )
	ensures output.Success? ==> HkdfExpandSucceededWith (  input , output.value )

 predicate {:opaque} HkdfExtractCalledWith ( input: HkdfExtractInput ) {true}
 predicate {:opaque} HkdfExtractSucceededWith (  input: HkdfExtractInput , output: seq<uint8> ) {true}
 method HkdfExtract ( input: HkdfExtractInput ) returns  ( output: Result<seq<uint8>, IAwsCryptographicPrimitivesException> )
	ensures HkdfExtractCalledWith (  input )
	ensures output.Success? ==> HkdfExtractSucceededWith (  input , output.value )

 predicate {:opaque} AESDecryptCalledWith ( input: AESDecryptInput ) {true}
 predicate {:opaque} AESDecryptSucceededWith (  input: AESDecryptInput , output: seq<uint8> ) {true}
 method AESDecrypt ( input: AESDecryptInput ) returns  ( output: Result<seq<uint8>, IAwsCryptographicPrimitivesException> )
	ensures AESDecryptCalledWith (  input )
	ensures output.Success? ==> AESDecryptSucceededWith (  input , output.value )

 predicate {:opaque} GenerateRandomBytesCalledWith ( input: GenerateRandomBytesInput ) {true}
 predicate {:opaque} GenerateRandomBytesSucceededWith (  input: GenerateRandomBytesInput , output: seq<uint8> ) {true}
 method GenerateRandomBytes ( input: GenerateRandomBytesInput ) returns  ( output: Result<seq<uint8>, IAwsCryptographicPrimitivesException> )
	ensures GenerateRandomBytesCalledWith (  input )
	ensures output.Success? ==> GenerateRandomBytesSucceededWith (  input , output.value )

 predicate {:opaque} HkdfCalledWith ( input: HkdfInput ) {true}
 predicate {:opaque} HkdfSucceededWith (  input: HkdfInput , output: seq<uint8> ) {true}
 method Hkdf ( input: HkdfInput ) returns  ( output: Result<seq<uint8>, IAwsCryptographicPrimitivesException> )
	ensures HkdfCalledWith (  input )
	ensures output.Success? ==> HkdfSucceededWith (  input , output.value )

 predicate {:opaque} AESEncryptCalledWith ( input: AESEncryptInput ) {true}
 predicate {:opaque} AESEncryptSucceededWith (  input: AESEncryptInput , output: AESEncryptOutput ) {true}
 method AESEncrypt ( input: AESEncryptInput ) returns  ( output: Result<AESEncryptOutput, IAwsCryptographicPrimitivesException> )
	ensures AESEncryptCalledWith (  input )
	ensures output.Success? ==> AESEncryptSucceededWith (  input , output.value )

}
 trait {:termination false} IAwsCryptographicPrimitivesClient {
 predicate {:opaque} CreateAtomicPrimitivesCalledWith ( input: AwsCryptographicPrimitivesVersion ) {true}
 predicate {:opaque} CreateAtomicPrimitivesSucceededWith (  input: AwsCryptographicPrimitivesVersion , output: IAtomicPrimitives ) {true}
 method CreateAtomicPrimitives ( input: AwsCryptographicPrimitivesVersion ) returns  ( output: Result<IAtomicPrimitives, IAwsCryptographicPrimitivesException> )
	ensures CreateAtomicPrimitivesCalledWith (  input )
	ensures output.Success? ==> CreateAtomicPrimitivesSucceededWith (  input , output.value )

}
 trait IAwsCryptographicPrimitivesException {
    function method GetMessage(): (message: string) reads this
}

 class UnknownAwsCryptographicPrimitivesError extends IAwsCryptographicPrimitivesException {
    var message: string

    constructor (message: string) {
        this.message := message;
    }

    function method GetMessage(): (message: string)
        reads this
    {
        this.message
    }
}

 class AwsCryptographicPrimitivesError extends IAwsCryptographicPrimitivesException {
    var message: string

    constructor (message: string) {
        this.message := message;
    }

    function method GetMessage(): (message: string)
        reads this
    {
        this.message
    }
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
	nameonly length: int64 )
 datatype HkdfExpandInput = HkdfExpandInput (
	nameonly digestAlgorithm: DigestAlgorithm ,
	nameonly prk: seq<uint8> ,
	nameonly info: Option<seq<uint8>> ,
	nameonly expectedLength: int64 )
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
	nameonly digestAlgorithm: Option<DigestAlgorithm> ,
	nameonly message: Option<seq<uint8>> )
}
