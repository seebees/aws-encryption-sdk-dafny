// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/StandardLibrary.dfy"
 include "../../Util/UTF8.dfy"
 include "../../AwsCryptographicMaterialProviders/Model/AwsCryptographyMaterialProvidersTypes.dfy"
 module AwsEncryptionSdkTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import AwsCryptographyMaterialProvidersTypes
 trait {:termination false} IAwsEncryptionSdkClient {
 predicate {:opaque} EncryptCalledWith ( input: EncryptInput ) {true}
 predicate {:opaque} EncryptSucceededWith (  input: EncryptInput , output: EncryptOutput ) {true}
 method Encrypt ( input: EncryptInput ) returns  ( output: Result<EncryptOutput, Error> )
	ensures EncryptCalledWith (  input )
	ensures output.Success? ==> EncryptSucceededWith (  input , output.value )

 predicate {:opaque} DecryptCalledWith ( input: DecryptInput ) {true}
 predicate {:opaque} DecryptSucceededWith (  input: DecryptInput , output: DecryptOutput ) {true}
 method Decrypt ( input: DecryptInput ) returns  ( output: Result<DecryptOutput, Error> )
	ensures DecryptCalledWith (  input )
	ensures output.Success? ==> DecryptSucceededWith (  input , output.value )

}
 datatype AwsEncryptionSdkConfig = | AwsEncryptionSdkConfig (
 nameonly commitmentPolicy: Option<AwsCryptographyMaterialProvidersTypes.CommitmentPolicy> ,
 nameonly maxEncryptedDataKeys: Option<CountingNumbers>
 )
 type CountingNumbers = x: int64 | IsValid_CountingNumbers(x) witness *
 predicate method IsValid_CountingNumbers(x: int64) {
 ( 1 <= x  )
}
 datatype DecryptInput = | DecryptInput (
 nameonly ciphertext: seq<uint8> ,
 nameonly materialsManager: Option<AwsCryptographyMaterialProvidersTypes.ICryptographicMaterialsManager> ,
 nameonly keyring: Option<AwsCryptographyMaterialProvidersTypes.IKeyring>
 )
 datatype DecryptOutput = | DecryptOutput (
 nameonly plaintext: seq<uint8> ,
 nameonly encryptionContext: AwsCryptographyMaterialProvidersTypes.EncryptionContext ,
 nameonly algorithmSuiteId: AwsCryptographyMaterialProvidersTypes.AlgorithmSuiteId
 )
 datatype EncryptInput = | EncryptInput (
 nameonly plaintext: seq<uint8> ,
 nameonly encryptionContext: Option<AwsCryptographyMaterialProvidersTypes.EncryptionContext> ,
 nameonly materialsManager: Option<AwsCryptographyMaterialProvidersTypes.ICryptographicMaterialsManager> ,
 nameonly keyring: Option<AwsCryptographyMaterialProvidersTypes.IKeyring> ,
 nameonly algorithmSuiteId: Option<AwsCryptographyMaterialProvidersTypes.AlgorithmSuiteId> ,
 nameonly frameLength: Option<int64>
 )
 datatype EncryptOutput = | EncryptOutput (
 nameonly ciphertext: seq<uint8> ,
 nameonly encryptionContext: AwsCryptographyMaterialProvidersTypes.EncryptionContext ,
 nameonly algorithmSuiteId: AwsCryptographyMaterialProvidersTypes.AlgorithmSuiteId
 )
 datatype Error =
 // Local Error structures are listed here
 | AwsEncryptionSdkException (
 nameonly message: string
 )
 // Any dependent models are listed here
 | AwsCryptographyMaterialProviders(awsCryptographyMaterialProviders: AwsCryptographyMaterialProvidersTypes.Error)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
