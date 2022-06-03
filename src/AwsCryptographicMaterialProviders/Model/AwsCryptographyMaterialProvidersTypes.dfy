// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/StandardLibrary.dfy"
 include "../../Util/UTF8.dfy"
 include "../../Crypto/Model/AwsCryptographyPrimitivesTypes.dfy"
 include "../../AWS-KMS/Model/ComAmazonawsKmsTypes.dfy"
 module AwsCryptographyMaterialProvidersTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import AwsCryptographyPrimitivesTypes
 import ComAmazonawsKmsTypes
 type AccountId = string
 type AccountIdList = seq<AccountId>
 datatype AesWrappingAlg =
	| ALG_AES128_GCM_IV12_TAG16
	| ALG_AES192_GCM_IV12_TAG16
	| ALG_AES256_GCM_IV12_TAG16
 datatype AlgorithmSuiteId =
	| ALG_AES_128_GCM_IV12_TAG16_NO_KDF
	| ALG_AES_192_GCM_IV12_TAG16_NO_KDF
	| ALG_AES_256_GCM_IV12_TAG16_NO_KDF
	| ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256
	| ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256
	| ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256
	| ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256
	| ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
	| ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
	| ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY
	| ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
 datatype AlgorithmSuiteInfo = | AlgorithmSuiteInfo (
 nameonly id: AlgorithmSuiteId ,
 nameonly encrypt: AwsCryptographyPrimitivesTypes.AES_GCM ,
 nameonly kdf: DerivationAlgorithm ,
 nameonly commitment: DerivationAlgorithm ,
 nameonly signature: SignatureAlgorithm
 )
 trait {:termination false} IAwsCryptographicMaterialProvidersClient
 {
 method CreateAwsKmsKeyring ( input: CreateAwsKmsKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsKeyringSucceededWith (  input , output.value )
 method CreateAwsKmsDiscoveryKeyring ( input: CreateAwsKmsDiscoveryKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsDiscoveryKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsDiscoveryKeyringSucceededWith (  input , output.value )
 method CreateAwsKmsMultiKeyring ( input: CreateAwsKmsMultiKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsMultiKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsMultiKeyringSucceededWith (  input , output.value )
 method CreateAwsKmsDiscoveryMultiKeyring ( input: CreateAwsKmsDiscoveryMultiKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsDiscoveryMultiKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsDiscoveryMultiKeyringSucceededWith (  input , output.value )
 method CreateAwsKmsMrkKeyring ( input: CreateAwsKmsMrkKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsMrkKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsMrkKeyringSucceededWith (  input , output.value )
 method CreateAwsKmsMrkMultiKeyring ( input: CreateAwsKmsMrkMultiKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsMrkMultiKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsMrkMultiKeyringSucceededWith (  input , output.value )
 method CreateAwsKmsMrkDiscoveryKeyring ( input: CreateAwsKmsMrkDiscoveryKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsMrkDiscoveryKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsMrkDiscoveryKeyringSucceededWith (  input , output.value )
 method CreateAwsKmsMrkDiscoveryMultiKeyring ( input: CreateAwsKmsMrkDiscoveryMultiKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateAwsKmsMrkDiscoveryMultiKeyringCalledWith (  input )
	ensures output.Success? ==> CreateAwsKmsMrkDiscoveryMultiKeyringSucceededWith (  input , output.value )
 method CreateMultiKeyring ( input: CreateMultiKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateMultiKeyringCalledWith (  input )
	ensures output.Success? ==> CreateMultiKeyringSucceededWith (  input , output.value )
 method CreateRawAesKeyring ( input: CreateRawAesKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateRawAesKeyringCalledWith (  input )
	ensures output.Success? ==> CreateRawAesKeyringSucceededWith (  input , output.value )
 method CreateRawRsaKeyring ( input: CreateRawRsaKeyringInput ) returns (output: Result<IKeyring, Error>)
	ensures CreateRawRsaKeyringCalledWith (  input )
	ensures output.Success? ==> CreateRawRsaKeyringSucceededWith (  input , output.value )
 method CreateDefaultCryptographicMaterialsManager ( input: CreateDefaultCryptographicMaterialsManagerInput ) returns (output: Result<ICryptographicMaterialsManager, Error>)
	ensures CreateDefaultCryptographicMaterialsManagerCalledWith (  input )
	ensures output.Success? ==> CreateDefaultCryptographicMaterialsManagerSucceededWith (  input , output.value )
 method CreateDefaultClientSupplier ( input: CreateDefaultClientSupplierInput ) returns (output: Result<IClientSupplier, Error>)
	ensures CreateDefaultClientSupplierCalledWith (  input )
	ensures output.Success? ==> CreateDefaultClientSupplierSucceededWith (  input , output.value )
 method InitializeEncryptionMaterials ( input: InitializeMaterialsInput ) returns (output: Result<EncryptionMaterials, Error>)
	ensures InitializeEncryptionMaterialsCalledWith (  input )
	ensures output.Success? ==> InitializeEncryptionMaterialsSucceededWith (  input , output.value )
 method InitializeDecryptionMaterials ( input: InitializeMaterialsInput ) returns (output: Result<DecryptionMaterials, Error>)
	ensures InitializeDecryptionMaterialsCalledWith (  input )
	ensures output.Success? ==> InitializeDecryptionMaterialsSucceededWith (  input , output.value )
 method ValidEncryptionMaterialsTransition ( input: ValidEncryptionMaterialsTransitionInput ) returns (output: Result<bool, Error>)
	ensures ValidEncryptionMaterialsTransitionCalledWith (  input )
	ensures output.Success? ==> ValidEncryptionMaterialsTransitionSucceededWith (  input , output.value )
 method ValidDecryptionMaterialsTransition ( input: ValidDecryptionMaterialsTransitionInput ) returns (output: Result<bool, Error>)
	ensures ValidDecryptionMaterialsTransitionCalledWith (  input )
	ensures output.Success? ==> ValidDecryptionMaterialsTransitionSucceededWith (  input , output.value )
}
 // Predicates are separated from the trait. This is temporary.
 predicate {:opaque} CreateAwsKmsKeyringCalledWith ( input: CreateAwsKmsKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsKeyringSucceededWith (  input: CreateAwsKmsKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateAwsKmsDiscoveryKeyringCalledWith ( input: CreateAwsKmsDiscoveryKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsDiscoveryKeyringSucceededWith (  input: CreateAwsKmsDiscoveryKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateAwsKmsMultiKeyringCalledWith ( input: CreateAwsKmsMultiKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsMultiKeyringSucceededWith (  input: CreateAwsKmsMultiKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateAwsKmsDiscoveryMultiKeyringCalledWith ( input: CreateAwsKmsDiscoveryMultiKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsDiscoveryMultiKeyringSucceededWith (  input: CreateAwsKmsDiscoveryMultiKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateAwsKmsMrkKeyringCalledWith ( input: CreateAwsKmsMrkKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsMrkKeyringSucceededWith (  input: CreateAwsKmsMrkKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateAwsKmsMrkMultiKeyringCalledWith ( input: CreateAwsKmsMrkMultiKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsMrkMultiKeyringSucceededWith (  input: CreateAwsKmsMrkMultiKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateAwsKmsMrkDiscoveryKeyringCalledWith ( input: CreateAwsKmsMrkDiscoveryKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsMrkDiscoveryKeyringSucceededWith (  input: CreateAwsKmsMrkDiscoveryKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateAwsKmsMrkDiscoveryMultiKeyringCalledWith ( input: CreateAwsKmsMrkDiscoveryMultiKeyringInput ) {true}
 predicate {:opaque} CreateAwsKmsMrkDiscoveryMultiKeyringSucceededWith (  input: CreateAwsKmsMrkDiscoveryMultiKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateMultiKeyringCalledWith ( input: CreateMultiKeyringInput ) {true}
 predicate {:opaque} CreateMultiKeyringSucceededWith (  input: CreateMultiKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateRawAesKeyringCalledWith ( input: CreateRawAesKeyringInput ) {true}
 predicate {:opaque} CreateRawAesKeyringSucceededWith (  input: CreateRawAesKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateRawRsaKeyringCalledWith ( input: CreateRawRsaKeyringInput ) {true}
 predicate {:opaque} CreateRawRsaKeyringSucceededWith (  input: CreateRawRsaKeyringInput , output: IKeyring ) {true}
 predicate {:opaque} CreateDefaultCryptographicMaterialsManagerCalledWith ( input: CreateDefaultCryptographicMaterialsManagerInput ) {true}
 predicate {:opaque} CreateDefaultCryptographicMaterialsManagerSucceededWith (  input: CreateDefaultCryptographicMaterialsManagerInput , output: ICryptographicMaterialsManager ) {true}
 predicate {:opaque} CreateDefaultClientSupplierCalledWith ( input: CreateDefaultClientSupplierInput ) {true}
 predicate {:opaque} CreateDefaultClientSupplierSucceededWith (  input: CreateDefaultClientSupplierInput , output: IClientSupplier ) {true}
 predicate {:opaque} InitializeEncryptionMaterialsCalledWith ( input: InitializeMaterialsInput ) {true}
 predicate {:opaque} InitializeEncryptionMaterialsSucceededWith (  input: InitializeMaterialsInput , output: EncryptionMaterials ) {true}
 predicate {:opaque} InitializeDecryptionMaterialsCalledWith ( input: InitializeMaterialsInput ) {true}
 predicate {:opaque} InitializeDecryptionMaterialsSucceededWith (  input: InitializeMaterialsInput , output: DecryptionMaterials ) {true}
 predicate {:opaque} ValidEncryptionMaterialsTransitionCalledWith ( input: ValidEncryptionMaterialsTransitionInput ) {true}
 predicate {:opaque} ValidEncryptionMaterialsTransitionSucceededWith (  input: ValidEncryptionMaterialsTransitionInput , output: bool ) {true}
 predicate {:opaque} ValidDecryptionMaterialsTransitionCalledWith ( input: ValidDecryptionMaterialsTransitionInput ) {true}
 predicate {:opaque} ValidDecryptionMaterialsTransitionSucceededWith (  input: ValidDecryptionMaterialsTransitionInput , output: bool ) {true}
 trait {:termination false} IClientSupplier
 {
 method GetClient ( input: GetClientInput ) returns (output: Result<ComAmazonawsKmsTypes.IKeyManagementServiceClient, Error>)
	ensures GetClientCalledWith (  input )
	ensures output.Success? ==> GetClientSucceededWith (  input , output.value )
}
 // Predicates are separated from the trait. This is temporary.
 predicate {:opaque} GetClientCalledWith ( input: GetClientInput ) {true}
 predicate {:opaque} GetClientSucceededWith (  input: GetClientInput , output: ComAmazonawsKmsTypes.IKeyManagementServiceClient ) {true}
 datatype CommitmentPolicy =
	| FORBID_ENCRYPT_ALLOW_DECRYPT
	| REQUIRE_ENCRYPT_ALLOW_DECRYPT
	| REQUIRE_ENCRYPT_REQUIRE_DECRYPT
 datatype CreateAwsKmsDiscoveryKeyringInput = | CreateAwsKmsDiscoveryKeyringInput (
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsDiscoveryMultiKeyringInput = | CreateAwsKmsDiscoveryMultiKeyringInput (
 nameonly regions: RegionList ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsKeyringInput = | CreateAwsKmsKeyringInput (
 nameonly kmsKeyId: KmsKeyId ,
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMrkDiscoveryKeyringInput = | CreateAwsKmsMrkDiscoveryKeyringInput (
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly grantTokens: Option<GrantTokenList> ,
 nameonly region: Region
 )
 datatype CreateAwsKmsMrkDiscoveryMultiKeyringInput = | CreateAwsKmsMrkDiscoveryMultiKeyringInput (
 nameonly regions: RegionList ,
 nameonly discoveryFilter: Option<DiscoveryFilter> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMrkKeyringInput = | CreateAwsKmsMrkKeyringInput (
 nameonly kmsKeyId: KmsKeyId ,
 nameonly kmsClient: ComAmazonawsKmsTypes.IKeyManagementServiceClient ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMrkMultiKeyringInput = | CreateAwsKmsMrkMultiKeyringInput (
 nameonly generator: Option<KmsKeyId> ,
 nameonly kmsKeyIds: Option<KmsKeyIdList> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateAwsKmsMultiKeyringInput = | CreateAwsKmsMultiKeyringInput (
 nameonly generator: Option<KmsKeyId> ,
 nameonly kmsKeyIds: Option<KmsKeyIdList> ,
 nameonly clientSupplier: Option<IClientSupplier> ,
 nameonly grantTokens: Option<GrantTokenList>
 )
 datatype CreateDefaultClientSupplierInput = | CreateDefaultClientSupplierInput (
 
 )
 datatype CreateDefaultCryptographicMaterialsManagerInput = | CreateDefaultCryptographicMaterialsManagerInput (
 nameonly keyring: IKeyring
 )
 datatype CreateMultiKeyringInput = | CreateMultiKeyringInput (
 nameonly generator: Option<IKeyring> ,
 nameonly childKeyrings: KeyringList
 )
 datatype CreateRawAesKeyringInput = | CreateRawAesKeyringInput (
 nameonly keyNamespace: string ,
 nameonly keyName: string ,
 nameonly wrappingKey: seq<uint8> ,
 nameonly wrappingAlg: AesWrappingAlg
 )
 datatype CreateRawRsaKeyringInput = | CreateRawRsaKeyringInput (
 nameonly keyNamespace: string ,
 nameonly keyName: string ,
 nameonly paddingScheme: PaddingScheme ,
 nameonly publicKey: Option<seq<uint8>> ,
 nameonly privateKey: Option<seq<uint8>>
 )
 trait {:termination false} ICryptographicMaterialsManager
 {
 method GetEncryptionMaterials ( input: GetEncryptionMaterialsInput ) returns (output: Result<GetEncryptionMaterialsOutput, Error>)
	ensures GetEncryptionMaterialsCalledWith (  input )
	ensures output.Success? ==> GetEncryptionMaterialsSucceededWith (  input , output.value )
 method DecryptMaterials ( input: DecryptMaterialsInput ) returns (output: Result<DecryptMaterialsOutput, Error>)
	ensures DecryptMaterialsCalledWith (  input )
	ensures output.Success? ==> DecryptMaterialsSucceededWith (  input , output.value )
}
 // Predicates are separated from the trait. This is temporary.
 predicate {:opaque} GetEncryptionMaterialsCalledWith ( input: GetEncryptionMaterialsInput ) {true}
 predicate {:opaque} GetEncryptionMaterialsSucceededWith (  input: GetEncryptionMaterialsInput , output: GetEncryptionMaterialsOutput ) {true}
 predicate {:opaque} DecryptMaterialsCalledWith ( input: DecryptMaterialsInput ) {true}
 predicate {:opaque} DecryptMaterialsSucceededWith (  input: DecryptMaterialsInput , output: DecryptMaterialsOutput ) {true}
 datatype DecryptionMaterials = | DecryptionMaterials (
 nameonly algorithmSuite: AlgorithmSuiteInfo ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly plaintextDataKey: Option<seq<uint8>> ,
 nameonly verificationKey: Option<seq<uint8>>
 )
 datatype DecryptMaterialsInput = | DecryptMaterialsInput (
 nameonly algorithmSuiteId: AlgorithmSuiteId ,
 nameonly commitmentPolicy: CommitmentPolicy ,
 nameonly encryptedDataKeys: EncryptedDataKeyList ,
 nameonly encryptionContext: EncryptionContext
 )
 datatype DecryptMaterialsOutput = | DecryptMaterialsOutput (
 nameonly decryptionMaterials: DecryptionMaterials
 )
 datatype DerivationAlgorithm =
 | HKDF(HKDF: HKDF)
 | IDENTITY(IDENTITY: IDENTITY)
 | None(None: None)
 datatype DiscoveryFilter = | DiscoveryFilter (
 nameonly accountIds: AccountIdList ,
 nameonly partition: string
 )
 datatype ECDSA = | ECDSA (
 nameonly curve: string
 )
 datatype EncryptedDataKey = | EncryptedDataKey (
 nameonly keyProviderId: Utf8Bytes ,
 nameonly keyProviderInfo: seq<uint8> ,
 nameonly ciphertext: seq<uint8>
 )
 type EncryptedDataKeyList = seq<EncryptedDataKey>
 type EncryptionContext = map<Utf8Bytes, Utf8Bytes>
 datatype EncryptionMaterials = | EncryptionMaterials (
 nameonly algorithmSuite: AlgorithmSuiteInfo ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly encryptedDataKeys: EncryptedDataKeyList ,
 nameonly plaintextDataKey: Option<seq<uint8>> ,
 nameonly signingKey: Option<seq<uint8>>
 )
 datatype GetClientInput = | GetClientInput (
 nameonly region: Region
 )
 datatype GetEncryptionMaterialsInput = | GetEncryptionMaterialsInput (
 nameonly encryptionContext: EncryptionContext ,
 nameonly commitmentPolicy: CommitmentPolicy ,
 nameonly algorithmSuiteId: Option<AlgorithmSuiteId> ,
 nameonly maxPlaintextLength: Option<int64>
 )
 datatype GetEncryptionMaterialsOutput = | GetEncryptionMaterialsOutput (
 nameonly encryptionMaterials: EncryptionMaterials
 )
 type GrantTokenList = seq<string>
 datatype HKDF = | HKDF (
 nameonly hmac: AwsCryptographyPrimitivesTypes.DigestAlgorithm ,
 nameonly saltLength: AwsCryptographyPrimitivesTypes.PositiveInteger ,
 nameonly inputKeyLength: AwsCryptographyPrimitivesTypes.PositiveInteger ,
 nameonly outputKeyLength: AwsCryptographyPrimitivesTypes.PositiveInteger
 )
 datatype IDENTITY = | IDENTITY (
 
 )
 datatype InitializeMaterialsInput = | InitializeMaterialsInput (
 nameonly algorithmSuiteId: AlgorithmSuiteId ,
 nameonly encryptionContext: EncryptionContext ,
 nameonly signingKey: Option<seq<uint8>>
 )
 type KeyringList = seq<IKeyring>
 trait {:termination false} IKeyring
 {
 method OnEncrypt ( input: OnEncryptInput ) returns (output: Result<OnEncryptOutput, Error>)
	ensures OnEncryptCalledWith (  input )
	ensures output.Success? ==> OnEncryptSucceededWith (  input , output.value )
 method OnDecrypt ( input: OnDecryptInput ) returns (output: Result<OnDecryptOutput, Error>)
	ensures OnDecryptCalledWith (  input )
	ensures output.Success? ==> OnDecryptSucceededWith (  input , output.value )
}
 // Predicates are separated from the trait. This is temporary.
 predicate {:opaque} OnEncryptCalledWith ( input: OnEncryptInput ) {true}
 predicate {:opaque} OnEncryptSucceededWith (  input: OnEncryptInput , output: OnEncryptOutput ) {true}
 predicate {:opaque} OnDecryptCalledWith ( input: OnDecryptInput ) {true}
 predicate {:opaque} OnDecryptSucceededWith (  input: OnDecryptInput , output: OnDecryptOutput ) {true}
 type KmsKeyId = string
 type KmsKeyIdList = seq<KmsKeyId>
 datatype MaterialProvidersConfig = | MaterialProvidersConfig (
 
 )
 datatype None = | None (
 
 )
 datatype OnDecryptInput = | OnDecryptInput (
 nameonly materials: DecryptionMaterials ,
 nameonly encryptedDataKeys: EncryptedDataKeyList
 )
 datatype OnDecryptOutput = | OnDecryptOutput (
 nameonly materials: DecryptionMaterials
 )
 datatype OnEncryptInput = | OnEncryptInput (
 nameonly materials: EncryptionMaterials
 )
 datatype OnEncryptOutput = | OnEncryptOutput (
 nameonly materials: EncryptionMaterials
 )
 datatype PaddingScheme =
	| PKCS1
	| OAEP_SHA1_MGF1
	| OAEP_SHA256_MGF1
	| OAEP_SHA384_MGF1
	| OAEP_SHA512_MGF1
 type Region = string
 type RegionList = seq<Region>
 datatype SignatureAlgorithm =
 | ECDSA(ECDSA: ECDSA)
 | None(None: None)
 type Utf8Bytes = ValidUTF8Bytes
 datatype ValidDecryptionMaterialsTransitionInput = | ValidDecryptionMaterialsTransitionInput (
 nameonly start: Option<DecryptionMaterials> ,
 nameonly stop: Option<DecryptionMaterials>
 )
 datatype ValidEncryptionMaterialsTransitionInput = | ValidEncryptionMaterialsTransitionInput (
 nameonly start: Option<EncryptionMaterials> ,
 nameonly stop: Option<EncryptionMaterials>
 )
 datatype Error =
 // Local Error structures are listed here
 | AwsCryptographicMaterialProvidersException (
 nameonly message: string
 )
 // Any dependent models are listed here
 | AwsCryptographyPrimitives(AwsCryptographyPrimitives: AwsCryptographyPrimitivesTypes.Error)
 | ComAmazonawsKms(ComAmazonawsKms: ComAmazonawsKmsTypes.Error)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AwsCryptographyMaterialProvidersAbstract
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = AwsCryptographyMaterialProvidersTypes
 function method DefaultMaterialProvidersConfig(): MaterialProvidersConfig
 method MaterialProviders(config: MaterialProvidersConfig := DefaultMaterialProvidersConfig())
 returns (res: Result<IAwsCryptographicMaterialProvidersClient, Error>)
}
