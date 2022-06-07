// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/StandardLibrary.dfy"
 include "../../Util/UTF8.dfy"
 module ComAmazonawsKmsTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 datatype AlgorithmSpec =
	| RSAES_PKCS1_V1_5
	| RSAES_OAEP_SHA_1
	| RSAES_OAEP_SHA_256
 type AliasList = seq<AliasListEntry>
 datatype AliasListEntry = | AliasListEntry (
 nameonly AliasName: Option<AliasNameType> ,
 nameonly AliasArn: Option<ArnType> ,
 nameonly TargetKeyId: Option<KeyIdType> ,
 nameonly CreationDate: Option<string> ,
 nameonly LastUpdatedDate: Option<string>
 )
 type AliasNameType = x: string | IsValid_AliasNameType(x) witness *
 predicate method IsValid_AliasNameType(x: string) {
 ( 1 <= |x| <= 256 )
}
 type ArnType = x: string | IsValid_ArnType(x) witness *
 predicate method IsValid_ArnType(x: string) {
 ( 20 <= |x| <= 2048 )
}
 type AWSAccountIdType = string
 type BooleanType = bool
 datatype CancelKeyDeletionRequest = | CancelKeyDeletionRequest (
 nameonly KeyId: KeyIdType
 )
 datatype CancelKeyDeletionResponse = | CancelKeyDeletionResponse (
 nameonly KeyId: Option<KeyIdType>
 )
 type CiphertextType = x: seq<uint8> | IsValid_CiphertextType(x) witness *
 predicate method IsValid_CiphertextType(x: seq<uint8>) {
 ( 1 <= |x| <= 6144 )
}
 type CloudHsmClusterIdType = x: string | IsValid_CloudHsmClusterIdType(x) witness *
 predicate method IsValid_CloudHsmClusterIdType(x: string) {
 ( 19 <= |x| <= 24 )
}
 datatype ConnectCustomKeyStoreRequest = | ConnectCustomKeyStoreRequest (
 nameonly CustomKeyStoreId: CustomKeyStoreIdType
 )
 datatype ConnectCustomKeyStoreResponse = | ConnectCustomKeyStoreResponse (
 
 )
 datatype ConnectionErrorCodeType =
	| INVALID_CREDENTIALS
	| CLUSTER_NOT_FOUND
	| NETWORK_ERRORS
	| INTERNAL_ERROR
	| INSUFFICIENT_CLOUDHSM_HSMS
	| USER_LOCKED_OUT
	| USER_NOT_FOUND
	| USER_LOGGED_IN
	| SUBNET_NOT_FOUND
 datatype ConnectionStateType =
	| CONNECTED
	| CONNECTING
	| FAILED
	| DISCONNECTED
	| DISCONNECTING
 datatype CreateAliasRequest = | CreateAliasRequest (
 nameonly AliasName: AliasNameType ,
 nameonly TargetKeyId: KeyIdType
 )
 datatype CreateCustomKeyStoreRequest = | CreateCustomKeyStoreRequest (
 nameonly CustomKeyStoreName: CustomKeyStoreNameType ,
 nameonly CloudHsmClusterId: CloudHsmClusterIdType ,
 nameonly TrustAnchorCertificate: TrustAnchorCertificateType ,
 nameonly KeyStorePassword: KeyStorePasswordType
 )
 datatype CreateCustomKeyStoreResponse = | CreateCustomKeyStoreResponse (
 nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>
 )
 datatype CreateGrantRequest = | CreateGrantRequest (
 nameonly KeyId: KeyIdType ,
 nameonly GranteePrincipal: PrincipalIdType ,
 nameonly RetiringPrincipal: Option<PrincipalIdType> ,
 nameonly Operations: GrantOperationList ,
 nameonly Constraints: Option<GrantConstraints> ,
 nameonly GrantTokens: Option<GrantTokenList> ,
 nameonly Name: Option<GrantNameType>
 )
 datatype CreateGrantResponse = | CreateGrantResponse (
 nameonly GrantToken: Option<GrantTokenType> ,
 nameonly GrantId: Option<GrantIdType>
 )
 datatype CreateKeyRequest = | CreateKeyRequest (
 nameonly Policy: Option<PolicyType> ,
 nameonly Description: Option<DescriptionType> ,
 nameonly KeyUsage: Option<KeyUsageType> ,
 nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> ,
 nameonly KeySpec: Option<KeySpec> ,
 nameonly Origin: Option<OriginType> ,
 nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
 nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> ,
 nameonly Tags: Option<TagList> ,
 nameonly MultiRegion: Option<NullableBooleanType>
 )
 datatype CreateKeyResponse = | CreateKeyResponse (
 nameonly KeyMetadata: Option<KeyMetadata>
 )
 datatype CustomerMasterKeySpec =
	| RSA_2048
	| RSA_3072
	| RSA_4096
	| ECC_NIST_P256
	| ECC_NIST_P384
	| ECC_NIST_P521
	| ECC_SECG_P256K1
	| SYMMETRIC_DEFAULT
 type CustomKeyStoreIdType = x: string | IsValid_CustomKeyStoreIdType(x) witness *
 predicate method IsValid_CustomKeyStoreIdType(x: string) {
 ( 1 <= |x| <= 64 )
}
 type CustomKeyStoreNameType = x: string | IsValid_CustomKeyStoreNameType(x) witness *
 predicate method IsValid_CustomKeyStoreNameType(x: string) {
 ( 1 <= |x| <= 256 )
}
 type CustomKeyStoresList = seq<CustomKeyStoresListEntry>
 datatype CustomKeyStoresListEntry = | CustomKeyStoresListEntry (
 nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
 nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType> ,
 nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> ,
 nameonly TrustAnchorCertificate: Option<TrustAnchorCertificateType> ,
 nameonly ConnectionState: Option<ConnectionStateType> ,
 nameonly ConnectionErrorCode: Option<ConnectionErrorCodeType> ,
 nameonly CreationDate: Option<string>
 )
 datatype DataKeyPairSpec =
	| RSA_2048
	| RSA_3072
	| RSA_4096
	| ECC_NIST_P256
	| ECC_NIST_P384
	| ECC_NIST_P521
	| ECC_SECG_P256K1
 datatype DataKeySpec =
	| AES_256
	| AES_128
 datatype DecryptRequest = | DecryptRequest (
 nameonly CiphertextBlob: CiphertextType ,
 nameonly EncryptionContext: Option<EncryptionContextType> ,
 nameonly GrantTokens: Option<GrantTokenList> ,
 nameonly KeyId: Option<KeyIdType> ,
 nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>
 )
 datatype DecryptResponse = | DecryptResponse (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly Plaintext: Option<PlaintextType> ,
 nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>
 )
 datatype DeleteAliasRequest = | DeleteAliasRequest (
 nameonly AliasName: AliasNameType
 )
 datatype DeleteCustomKeyStoreRequest = | DeleteCustomKeyStoreRequest (
 nameonly CustomKeyStoreId: CustomKeyStoreIdType
 )
 datatype DeleteCustomKeyStoreResponse = | DeleteCustomKeyStoreResponse (
 
 )
 datatype DeleteImportedKeyMaterialRequest = | DeleteImportedKeyMaterialRequest (
 nameonly KeyId: KeyIdType
 )
 datatype DescribeCustomKeyStoresRequest = | DescribeCustomKeyStoresRequest (
 nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
 nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType> ,
 nameonly Limit: Option<LimitType> ,
 nameonly Marker: Option<MarkerType>
 )
 datatype DescribeCustomKeyStoresResponse = | DescribeCustomKeyStoresResponse (
 nameonly CustomKeyStores: Option<CustomKeyStoresList> ,
 nameonly NextMarker: Option<MarkerType> ,
 nameonly Truncated: Option<BooleanType>
 )
 datatype DescribeKeyRequest = | DescribeKeyRequest (
 nameonly KeyId: KeyIdType ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype DescribeKeyResponse = | DescribeKeyResponse (
 nameonly KeyMetadata: Option<KeyMetadata>
 )
 type DescriptionType = x: string | IsValid_DescriptionType(x) witness *
 predicate method IsValid_DescriptionType(x: string) {
 ( 0 <= |x| <= 8192 )
}
 datatype DisableKeyRequest = | DisableKeyRequest (
 nameonly KeyId: KeyIdType
 )
 datatype DisableKeyRotationRequest = | DisableKeyRotationRequest (
 nameonly KeyId: KeyIdType
 )
 datatype DisconnectCustomKeyStoreRequest = | DisconnectCustomKeyStoreRequest (
 nameonly CustomKeyStoreId: CustomKeyStoreIdType
 )
 datatype DisconnectCustomKeyStoreResponse = | DisconnectCustomKeyStoreResponse (
 
 )
 datatype EnableKeyRequest = | EnableKeyRequest (
 nameonly KeyId: KeyIdType
 )
 datatype EnableKeyRotationRequest = | EnableKeyRotationRequest (
 nameonly KeyId: KeyIdType
 )
 datatype EncryptionAlgorithmSpec =
	| SYMMETRIC_DEFAULT
	| RSAES_OAEP_SHA_1
	| RSAES_OAEP_SHA_256
 type EncryptionAlgorithmSpecList = seq<EncryptionAlgorithmSpec>
 type EncryptionContextKey = string
 type EncryptionContextType = map<EncryptionContextKey, EncryptionContextValue>
 type EncryptionContextValue = string
 datatype EncryptRequest = | EncryptRequest (
 nameonly KeyId: KeyIdType ,
 nameonly Plaintext: PlaintextType ,
 nameonly EncryptionContext: Option<EncryptionContextType> ,
 nameonly GrantTokens: Option<GrantTokenList> ,
 nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>
 )
 datatype EncryptResponse = | EncryptResponse (
 nameonly CiphertextBlob: Option<CiphertextType> ,
 nameonly KeyId: Option<KeyIdType> ,
 nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>
 )
 type ErrorMessageType = string
 datatype ExpirationModelType =
	| KEY_MATERIAL_EXPIRES
	| KEY_MATERIAL_DOES_NOT_EXPIRE
 datatype GenerateDataKeyPairRequest = | GenerateDataKeyPairRequest (
 nameonly EncryptionContext: Option<EncryptionContextType> ,
 nameonly KeyId: KeyIdType ,
 nameonly KeyPairSpec: DataKeyPairSpec ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype GenerateDataKeyPairResponse = | GenerateDataKeyPairResponse (
 nameonly PrivateKeyCiphertextBlob: Option<CiphertextType> ,
 nameonly PrivateKeyPlaintext: Option<PlaintextType> ,
 nameonly PublicKey: Option<PublicKeyType> ,
 nameonly KeyId: Option<KeyIdType> ,
 nameonly KeyPairSpec: Option<DataKeyPairSpec>
 )
 datatype GenerateDataKeyPairWithoutPlaintextRequest = | GenerateDataKeyPairWithoutPlaintextRequest (
 nameonly EncryptionContext: Option<EncryptionContextType> ,
 nameonly KeyId: KeyIdType ,
 nameonly KeyPairSpec: DataKeyPairSpec ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype GenerateDataKeyPairWithoutPlaintextResponse = | GenerateDataKeyPairWithoutPlaintextResponse (
 nameonly PrivateKeyCiphertextBlob: Option<CiphertextType> ,
 nameonly PublicKey: Option<PublicKeyType> ,
 nameonly KeyId: Option<KeyIdType> ,
 nameonly KeyPairSpec: Option<DataKeyPairSpec>
 )
 datatype GenerateDataKeyRequest = | GenerateDataKeyRequest (
 nameonly KeyId: KeyIdType ,
 nameonly EncryptionContext: Option<EncryptionContextType> ,
 nameonly NumberOfBytes: Option<NumberOfBytesType> ,
 nameonly KeySpec: Option<DataKeySpec> ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype GenerateDataKeyResponse = | GenerateDataKeyResponse (
 nameonly CiphertextBlob: Option<CiphertextType> ,
 nameonly Plaintext: Option<PlaintextType> ,
 nameonly KeyId: Option<KeyIdType>
 )
 datatype GenerateDataKeyWithoutPlaintextRequest = | GenerateDataKeyWithoutPlaintextRequest (
 nameonly KeyId: KeyIdType ,
 nameonly EncryptionContext: Option<EncryptionContextType> ,
 nameonly KeySpec: Option<DataKeySpec> ,
 nameonly NumberOfBytes: Option<NumberOfBytesType> ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype GenerateDataKeyWithoutPlaintextResponse = | GenerateDataKeyWithoutPlaintextResponse (
 nameonly CiphertextBlob: Option<CiphertextType> ,
 nameonly KeyId: Option<KeyIdType>
 )
 datatype GenerateRandomRequest = | GenerateRandomRequest (
 nameonly NumberOfBytes: Option<NumberOfBytesType> ,
 nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>
 )
 datatype GenerateRandomResponse = | GenerateRandomResponse (
 nameonly Plaintext: Option<PlaintextType>
 )
 datatype GetKeyPolicyRequest = | GetKeyPolicyRequest (
 nameonly KeyId: KeyIdType ,
 nameonly PolicyName: PolicyNameType
 )
 datatype GetKeyPolicyResponse = | GetKeyPolicyResponse (
 nameonly Policy: Option<PolicyType>
 )
 datatype GetKeyRotationStatusRequest = | GetKeyRotationStatusRequest (
 nameonly KeyId: KeyIdType
 )
 datatype GetKeyRotationStatusResponse = | GetKeyRotationStatusResponse (
 nameonly KeyRotationEnabled: Option<BooleanType>
 )
 datatype GetParametersForImportRequest = | GetParametersForImportRequest (
 nameonly KeyId: KeyIdType ,
 nameonly WrappingAlgorithm: AlgorithmSpec ,
 nameonly WrappingKeySpec: WrappingKeySpec
 )
 datatype GetParametersForImportResponse = | GetParametersForImportResponse (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly ImportToken: Option<CiphertextType> ,
 nameonly PublicKey: Option<PlaintextType> ,
 nameonly ParametersValidTo: Option<string>
 )
 datatype GetPublicKeyRequest = | GetPublicKeyRequest (
 nameonly KeyId: KeyIdType ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype GetPublicKeyResponse = | GetPublicKeyResponse (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly PublicKey: Option<PublicKeyType> ,
 nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> ,
 nameonly KeySpec: Option<KeySpec> ,
 nameonly KeyUsage: Option<KeyUsageType> ,
 nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList> ,
 nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList>
 )
 datatype GrantConstraints = | GrantConstraints (
 nameonly EncryptionContextSubset: Option<EncryptionContextType> ,
 nameonly EncryptionContextEquals: Option<EncryptionContextType>
 )
 type GrantIdType = x: string | IsValid_GrantIdType(x) witness *
 predicate method IsValid_GrantIdType(x: string) {
 ( 1 <= |x| <= 128 )
}
 type GrantList = seq<GrantListEntry>
 datatype GrantListEntry = | GrantListEntry (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly GrantId: Option<GrantIdType> ,
 nameonly Name: Option<GrantNameType> ,
 nameonly CreationDate: Option<string> ,
 nameonly GranteePrincipal: Option<PrincipalIdType> ,
 nameonly RetiringPrincipal: Option<PrincipalIdType> ,
 nameonly IssuingAccount: Option<PrincipalIdType> ,
 nameonly Operations: Option<GrantOperationList> ,
 nameonly Constraints: Option<GrantConstraints>
 )
 type GrantNameType = x: string | IsValid_GrantNameType(x) witness *
 predicate method IsValid_GrantNameType(x: string) {
 ( 1 <= |x| <= 256 )
}
 datatype GrantOperation =
	| Decrypt
	| Encrypt
	| GenerateDataKey
	| GenerateDataKeyWithoutPlaintext
	| ReEncryptFrom
	| ReEncryptTo
	| Sign
	| Verify
	| GetPublicKey
	| CreateGrant
	| RetireGrant
	| DescribeKey
	| GenerateDataKeyPair
	| GenerateDataKeyPairWithoutPlaintext
 type GrantOperationList = seq<GrantOperation>
 type GrantTokenList = x: seq<GrantTokenType> | IsValid_GrantTokenList(x) witness *
 predicate method IsValid_GrantTokenList(x: seq<GrantTokenType>) {
 ( 0 <= |x| <= 10 )
}
 type GrantTokenType = x: string | IsValid_GrantTokenType(x) witness *
 predicate method IsValid_GrantTokenType(x: string) {
 ( 1 <= |x| <= 8192 )
}
 datatype ImportKeyMaterialRequest = | ImportKeyMaterialRequest (
 nameonly KeyId: KeyIdType ,
 nameonly ImportToken: CiphertextType ,
 nameonly EncryptedKeyMaterial: CiphertextType ,
 nameonly ValidTo: Option<string> ,
 nameonly ExpirationModel: Option<ExpirationModelType>
 )
 datatype ImportKeyMaterialResponse = | ImportKeyMaterialResponse (
 
 )
 type KeyIdType = x: string | IsValid_KeyIdType(x) witness *
 predicate method IsValid_KeyIdType(x: string) {
 ( 1 <= |x| <= 2048 )
}
 type KeyList = seq<KeyListEntry>
 datatype KeyListEntry = | KeyListEntry (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly KeyArn: Option<ArnType>
 )
 trait {:termination false} IKeyManagementServiceClient
 {
 method  CancelKeyDeletion
 ( input: CancelKeyDeletionRequest )
 returns (output: Result<CancelKeyDeletionResponse, Error>)
  ensures CancelKeyDeletionCalledWith (  input )
 ensures output.Success? ==> CancelKeyDeletionSucceededWith (  input , output.value )
 method  ConnectCustomKeyStore
 ( input: ConnectCustomKeyStoreRequest )
 returns (output: Result<ConnectCustomKeyStoreResponse, Error>)
  ensures ConnectCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> ConnectCustomKeyStoreSucceededWith (  input , output.value )
 method  CreateAlias
 ( input: CreateAliasRequest )
 returns (output: Result<(), Error>)
  ensures CreateAliasCalledWith (  input )
 ensures output.Success? ==> CreateAliasSucceededWith (  input )
 method  CreateCustomKeyStore
 ( input: CreateCustomKeyStoreRequest )
 returns (output: Result<CreateCustomKeyStoreResponse, Error>)
  ensures CreateCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> CreateCustomKeyStoreSucceededWith (  input , output.value )
 method  CreateGrant
 ( input: CreateGrantRequest )
 returns (output: Result<CreateGrantResponse, Error>)
  ensures CreateGrantCalledWith (  input )
 ensures output.Success? ==> CreateGrantSucceededWith (  input , output.value )
 method  CreateKey
 ( input: CreateKeyRequest )
 returns (output: Result<CreateKeyResponse, Error>)
  ensures CreateKeyCalledWith (  input )
 ensures output.Success? ==> CreateKeySucceededWith (  input , output.value )
 method  Decrypt
 ( input: DecryptRequest )
 returns (output: Result<DecryptResponse, Error>)
  ensures DecryptCalledWith (  input )
 ensures output.Success? ==> DecryptSucceededWith (  input , output.value )
 method  DeleteAlias
 ( input: DeleteAliasRequest )
 returns (output: Result<(), Error>)
  ensures DeleteAliasCalledWith (  input )
 ensures output.Success? ==> DeleteAliasSucceededWith (  input )
 method  DeleteCustomKeyStore
 ( input: DeleteCustomKeyStoreRequest )
 returns (output: Result<DeleteCustomKeyStoreResponse, Error>)
  ensures DeleteCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> DeleteCustomKeyStoreSucceededWith (  input , output.value )
 method  DeleteImportedKeyMaterial
 ( input: DeleteImportedKeyMaterialRequest )
 returns (output: Result<(), Error>)
  ensures DeleteImportedKeyMaterialCalledWith (  input )
 ensures output.Success? ==> DeleteImportedKeyMaterialSucceededWith (  input )
 method  DescribeCustomKeyStores
 ( input: DescribeCustomKeyStoresRequest )
 returns (output: Result<DescribeCustomKeyStoresResponse, Error>)
  ensures DescribeCustomKeyStoresCalledWith (  input )
 ensures output.Success? ==> DescribeCustomKeyStoresSucceededWith (  input , output.value )
 method  DescribeKey
 ( input: DescribeKeyRequest )
 returns (output: Result<DescribeKeyResponse, Error>)
  ensures DescribeKeyCalledWith (  input )
 ensures output.Success? ==> DescribeKeySucceededWith (  input , output.value )
 method  DisableKey
 ( input: DisableKeyRequest )
 returns (output: Result<(), Error>)
  ensures DisableKeyCalledWith (  input )
 ensures output.Success? ==> DisableKeySucceededWith (  input )
 method  DisableKeyRotation
 ( input: DisableKeyRotationRequest )
 returns (output: Result<(), Error>)
  ensures DisableKeyRotationCalledWith (  input )
 ensures output.Success? ==> DisableKeyRotationSucceededWith (  input )
 method  DisconnectCustomKeyStore
 ( input: DisconnectCustomKeyStoreRequest )
 returns (output: Result<DisconnectCustomKeyStoreResponse, Error>)
  ensures DisconnectCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> DisconnectCustomKeyStoreSucceededWith (  input , output.value )
 method  EnableKey
 ( input: EnableKeyRequest )
 returns (output: Result<(), Error>)
  ensures EnableKeyCalledWith (  input )
 ensures output.Success? ==> EnableKeySucceededWith (  input )
 method  EnableKeyRotation
 ( input: EnableKeyRotationRequest )
 returns (output: Result<(), Error>)
  ensures EnableKeyRotationCalledWith (  input )
 ensures output.Success? ==> EnableKeyRotationSucceededWith (  input )
 method  Encrypt
 ( input: EncryptRequest )
 returns (output: Result<EncryptResponse, Error>)
  ensures EncryptCalledWith (  input )
 ensures output.Success? ==> EncryptSucceededWith (  input , output.value )
 method  GenerateDataKey
 ( input: GenerateDataKeyRequest )
 returns (output: Result<GenerateDataKeyResponse, Error>)
  ensures GenerateDataKeyCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeySucceededWith (  input , output.value )
 method  GenerateDataKeyPair
 ( input: GenerateDataKeyPairRequest )
 returns (output: Result<GenerateDataKeyPairResponse, Error>)
  ensures GenerateDataKeyPairCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeyPairSucceededWith (  input , output.value )
 method  GenerateDataKeyPairWithoutPlaintext
 ( input: GenerateDataKeyPairWithoutPlaintextRequest )
 returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
  ensures GenerateDataKeyPairWithoutPlaintextCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeyPairWithoutPlaintextSucceededWith (  input , output.value )
 method  GenerateDataKeyWithoutPlaintext
 ( input: GenerateDataKeyWithoutPlaintextRequest )
 returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
  ensures GenerateDataKeyWithoutPlaintextCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeyWithoutPlaintextSucceededWith (  input , output.value )
 method  GenerateRandom
 ( input: GenerateRandomRequest )
 returns (output: Result<GenerateRandomResponse, Error>)
  ensures GenerateRandomCalledWith (  input )
 ensures output.Success? ==> GenerateRandomSucceededWith (  input , output.value )
 method  GetKeyPolicy
 ( input: GetKeyPolicyRequest )
 returns (output: Result<GetKeyPolicyResponse, Error>)
  ensures GetKeyPolicyCalledWith (  input )
 ensures output.Success? ==> GetKeyPolicySucceededWith (  input , output.value )
 method  GetKeyRotationStatus
 ( input: GetKeyRotationStatusRequest )
 returns (output: Result<GetKeyRotationStatusResponse, Error>)
  ensures GetKeyRotationStatusCalledWith (  input )
 ensures output.Success? ==> GetKeyRotationStatusSucceededWith (  input , output.value )
 method  GetParametersForImport
 ( input: GetParametersForImportRequest )
 returns (output: Result<GetParametersForImportResponse, Error>)
  ensures GetParametersForImportCalledWith (  input )
 ensures output.Success? ==> GetParametersForImportSucceededWith (  input , output.value )
 method  GetPublicKey
 ( input: GetPublicKeyRequest )
 returns (output: Result<GetPublicKeyResponse, Error>)
  ensures GetPublicKeyCalledWith (  input )
 ensures output.Success? ==> GetPublicKeySucceededWith (  input , output.value )
 method  ImportKeyMaterial
 ( input: ImportKeyMaterialRequest )
 returns (output: Result<ImportKeyMaterialResponse, Error>)
  ensures ImportKeyMaterialCalledWith (  input )
 ensures output.Success? ==> ImportKeyMaterialSucceededWith (  input , output.value )
 method  ListAliases
 ( input: ListAliasesRequest )
 returns (output: Result<ListAliasesResponse, Error>)
  ensures ListAliasesCalledWith (  input )
 ensures output.Success? ==> ListAliasesSucceededWith (  input , output.value )
 method  ListGrants
 ( input: ListGrantsRequest )
 returns (output: Result<ListGrantsResponse, Error>)
  ensures ListGrantsCalledWith (  input )
 ensures output.Success? ==> ListGrantsSucceededWith (  input , output.value )
 method  ListKeyPolicies
 ( input: ListKeyPoliciesRequest )
 returns (output: Result<ListKeyPoliciesResponse, Error>)
  ensures ListKeyPoliciesCalledWith (  input )
 ensures output.Success? ==> ListKeyPoliciesSucceededWith (  input , output.value )
 method  ListResourceTags
 ( input: ListResourceTagsRequest )
 returns (output: Result<ListResourceTagsResponse, Error>)
  ensures ListResourceTagsCalledWith (  input )
 ensures output.Success? ==> ListResourceTagsSucceededWith (  input , output.value )
 method  PutKeyPolicy
 ( input: PutKeyPolicyRequest )
 returns (output: Result<(), Error>)
  ensures PutKeyPolicyCalledWith (  input )
 ensures output.Success? ==> PutKeyPolicySucceededWith (  input )
 method  ReEncrypt
 ( input: ReEncryptRequest )
 returns (output: Result<ReEncryptResponse, Error>)
  ensures ReEncryptCalledWith (  input )
 ensures output.Success? ==> ReEncryptSucceededWith (  input , output.value )
 method  ReplicateKey
 ( input: ReplicateKeyRequest )
 returns (output: Result<ReplicateKeyResponse, Error>)
  ensures ReplicateKeyCalledWith (  input )
 ensures output.Success? ==> ReplicateKeySucceededWith (  input , output.value )
 method  RetireGrant
 ( input: RetireGrantRequest )
 returns (output: Result<(), Error>)
  ensures RetireGrantCalledWith (  input )
 ensures output.Success? ==> RetireGrantSucceededWith (  input )
 method  RevokeGrant
 ( input: RevokeGrantRequest )
 returns (output: Result<(), Error>)
  ensures RevokeGrantCalledWith (  input )
 ensures output.Success? ==> RevokeGrantSucceededWith (  input )
 method  ScheduleKeyDeletion
 ( input: ScheduleKeyDeletionRequest )
 returns (output: Result<ScheduleKeyDeletionResponse, Error>)
  ensures ScheduleKeyDeletionCalledWith (  input )
 ensures output.Success? ==> ScheduleKeyDeletionSucceededWith (  input , output.value )
 method  Sign
 ( input: SignRequest )
 returns (output: Result<SignResponse, Error>)
  ensures SignCalledWith (  input )
 ensures output.Success? ==> SignSucceededWith (  input , output.value )
 method  TagResource
 ( input: TagResourceRequest )
 returns (output: Result<(), Error>)
  ensures TagResourceCalledWith (  input )
 ensures output.Success? ==> TagResourceSucceededWith (  input )
 method  UntagResource
 ( input: UntagResourceRequest )
 returns (output: Result<(), Error>)
  ensures UntagResourceCalledWith (  input )
 ensures output.Success? ==> UntagResourceSucceededWith (  input )
 method  UpdateAlias
 ( input: UpdateAliasRequest )
 returns (output: Result<(), Error>)
  ensures UpdateAliasCalledWith (  input )
 ensures output.Success? ==> UpdateAliasSucceededWith (  input )
 method  UpdateCustomKeyStore
 ( input: UpdateCustomKeyStoreRequest )
 returns (output: Result<UpdateCustomKeyStoreResponse, Error>)
  ensures UpdateCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> UpdateCustomKeyStoreSucceededWith (  input , output.value )
 method  UpdateKeyDescription
 ( input: UpdateKeyDescriptionRequest )
 returns (output: Result<(), Error>)
  ensures UpdateKeyDescriptionCalledWith (  input )
 ensures output.Success? ==> UpdateKeyDescriptionSucceededWith (  input )
 method  UpdatePrimaryRegion
 ( input: UpdatePrimaryRegionRequest )
 returns (output: Result<(), Error>)
  ensures UpdatePrimaryRegionCalledWith (  input )
 ensures output.Success? ==> UpdatePrimaryRegionSucceededWith (  input )
 method  Verify
 ( input: VerifyRequest )
 returns (output: Result<VerifyResponse, Error>)
  ensures VerifyCalledWith (  input )
 ensures output.Success? ==> VerifySucceededWith (  input , output.value )
}
 // Predicates are separated from the trait. This is temporary.
 predicate {:opaque} CancelKeyDeletionCalledWith ( input: CancelKeyDeletionRequest ) {true}
 predicate {:opaque} CancelKeyDeletionSucceededWith (  input: CancelKeyDeletionRequest , output: CancelKeyDeletionResponse ) {true}
 predicate {:opaque} ConnectCustomKeyStoreCalledWith ( input: ConnectCustomKeyStoreRequest ) {true}
 predicate {:opaque} ConnectCustomKeyStoreSucceededWith (  input: ConnectCustomKeyStoreRequest , output: ConnectCustomKeyStoreResponse ) {true}
 predicate {:opaque} CreateAliasCalledWith ( input: CreateAliasRequest ) {true}
 predicate {:opaque} CreateAliasSucceededWith (  input: CreateAliasRequest ) {true}
 predicate {:opaque} CreateCustomKeyStoreCalledWith ( input: CreateCustomKeyStoreRequest ) {true}
 predicate {:opaque} CreateCustomKeyStoreSucceededWith (  input: CreateCustomKeyStoreRequest , output: CreateCustomKeyStoreResponse ) {true}
 predicate {:opaque} CreateGrantCalledWith ( input: CreateGrantRequest ) {true}
 predicate {:opaque} CreateGrantSucceededWith (  input: CreateGrantRequest , output: CreateGrantResponse ) {true}
 predicate {:opaque} CreateKeyCalledWith ( input: CreateKeyRequest ) {true}
 predicate {:opaque} CreateKeySucceededWith (  input: CreateKeyRequest , output: CreateKeyResponse ) {true}
 predicate {:opaque} DecryptCalledWith ( input: DecryptRequest ) {true}
 predicate {:opaque} DecryptSucceededWith (  input: DecryptRequest , output: DecryptResponse ) {true}
 predicate {:opaque} DeleteAliasCalledWith ( input: DeleteAliasRequest ) {true}
 predicate {:opaque} DeleteAliasSucceededWith (  input: DeleteAliasRequest ) {true}
 predicate {:opaque} DeleteCustomKeyStoreCalledWith ( input: DeleteCustomKeyStoreRequest ) {true}
 predicate {:opaque} DeleteCustomKeyStoreSucceededWith (  input: DeleteCustomKeyStoreRequest , output: DeleteCustomKeyStoreResponse ) {true}
 predicate {:opaque} DeleteImportedKeyMaterialCalledWith ( input: DeleteImportedKeyMaterialRequest ) {true}
 predicate {:opaque} DeleteImportedKeyMaterialSucceededWith (  input: DeleteImportedKeyMaterialRequest ) {true}
 predicate {:opaque} DescribeCustomKeyStoresCalledWith ( input: DescribeCustomKeyStoresRequest ) {true}
 predicate {:opaque} DescribeCustomKeyStoresSucceededWith (  input: DescribeCustomKeyStoresRequest , output: DescribeCustomKeyStoresResponse ) {true}
 predicate {:opaque} DescribeKeyCalledWith ( input: DescribeKeyRequest ) {true}
 predicate {:opaque} DescribeKeySucceededWith (  input: DescribeKeyRequest , output: DescribeKeyResponse ) {true}
 predicate {:opaque} DisableKeyCalledWith ( input: DisableKeyRequest ) {true}
 predicate {:opaque} DisableKeySucceededWith (  input: DisableKeyRequest ) {true}
 predicate {:opaque} DisableKeyRotationCalledWith ( input: DisableKeyRotationRequest ) {true}
 predicate {:opaque} DisableKeyRotationSucceededWith (  input: DisableKeyRotationRequest ) {true}
 predicate {:opaque} DisconnectCustomKeyStoreCalledWith ( input: DisconnectCustomKeyStoreRequest ) {true}
 predicate {:opaque} DisconnectCustomKeyStoreSucceededWith (  input: DisconnectCustomKeyStoreRequest , output: DisconnectCustomKeyStoreResponse ) {true}
 predicate {:opaque} EnableKeyCalledWith ( input: EnableKeyRequest ) {true}
 predicate {:opaque} EnableKeySucceededWith (  input: EnableKeyRequest ) {true}
 predicate {:opaque} EnableKeyRotationCalledWith ( input: EnableKeyRotationRequest ) {true}
 predicate {:opaque} EnableKeyRotationSucceededWith (  input: EnableKeyRotationRequest ) {true}
 predicate {:opaque} EncryptCalledWith ( input: EncryptRequest ) {true}
 predicate {:opaque} EncryptSucceededWith (  input: EncryptRequest , output: EncryptResponse ) {true}
 predicate {:opaque} GenerateDataKeyCalledWith ( input: GenerateDataKeyRequest ) {true}
 predicate {:opaque} GenerateDataKeySucceededWith (  input: GenerateDataKeyRequest , output: GenerateDataKeyResponse ) {true}
 predicate {:opaque} GenerateDataKeyPairCalledWith ( input: GenerateDataKeyPairRequest ) {true}
 predicate {:opaque} GenerateDataKeyPairSucceededWith (  input: GenerateDataKeyPairRequest , output: GenerateDataKeyPairResponse ) {true}
 predicate {:opaque} GenerateDataKeyPairWithoutPlaintextCalledWith ( input: GenerateDataKeyPairWithoutPlaintextRequest ) {true}
 predicate {:opaque} GenerateDataKeyPairWithoutPlaintextSucceededWith (  input: GenerateDataKeyPairWithoutPlaintextRequest , output: GenerateDataKeyPairWithoutPlaintextResponse ) {true}
 predicate {:opaque} GenerateDataKeyWithoutPlaintextCalledWith ( input: GenerateDataKeyWithoutPlaintextRequest ) {true}
 predicate {:opaque} GenerateDataKeyWithoutPlaintextSucceededWith (  input: GenerateDataKeyWithoutPlaintextRequest , output: GenerateDataKeyWithoutPlaintextResponse ) {true}
 predicate {:opaque} GenerateRandomCalledWith ( input: GenerateRandomRequest ) {true}
 predicate {:opaque} GenerateRandomSucceededWith (  input: GenerateRandomRequest , output: GenerateRandomResponse ) {true}
 predicate {:opaque} GetKeyPolicyCalledWith ( input: GetKeyPolicyRequest ) {true}
 predicate {:opaque} GetKeyPolicySucceededWith (  input: GetKeyPolicyRequest , output: GetKeyPolicyResponse ) {true}
 predicate {:opaque} GetKeyRotationStatusCalledWith ( input: GetKeyRotationStatusRequest ) {true}
 predicate {:opaque} GetKeyRotationStatusSucceededWith (  input: GetKeyRotationStatusRequest , output: GetKeyRotationStatusResponse ) {true}
 predicate {:opaque} GetParametersForImportCalledWith ( input: GetParametersForImportRequest ) {true}
 predicate {:opaque} GetParametersForImportSucceededWith (  input: GetParametersForImportRequest , output: GetParametersForImportResponse ) {true}
 predicate {:opaque} GetPublicKeyCalledWith ( input: GetPublicKeyRequest ) {true}
 predicate {:opaque} GetPublicKeySucceededWith (  input: GetPublicKeyRequest , output: GetPublicKeyResponse ) {true}
 predicate {:opaque} ImportKeyMaterialCalledWith ( input: ImportKeyMaterialRequest ) {true}
 predicate {:opaque} ImportKeyMaterialSucceededWith (  input: ImportKeyMaterialRequest , output: ImportKeyMaterialResponse ) {true}
 predicate {:opaque} ListAliasesCalledWith ( input: ListAliasesRequest ) {true}
 predicate {:opaque} ListAliasesSucceededWith (  input: ListAliasesRequest , output: ListAliasesResponse ) {true}
 predicate {:opaque} ListGrantsCalledWith ( input: ListGrantsRequest ) {true}
 predicate {:opaque} ListGrantsSucceededWith (  input: ListGrantsRequest , output: ListGrantsResponse ) {true}
 predicate {:opaque} ListKeyPoliciesCalledWith ( input: ListKeyPoliciesRequest ) {true}
 predicate {:opaque} ListKeyPoliciesSucceededWith (  input: ListKeyPoliciesRequest , output: ListKeyPoliciesResponse ) {true}
 predicate {:opaque} ListResourceTagsCalledWith ( input: ListResourceTagsRequest ) {true}
 predicate {:opaque} ListResourceTagsSucceededWith (  input: ListResourceTagsRequest , output: ListResourceTagsResponse ) {true}
 predicate {:opaque} PutKeyPolicyCalledWith ( input: PutKeyPolicyRequest ) {true}
 predicate {:opaque} PutKeyPolicySucceededWith (  input: PutKeyPolicyRequest ) {true}
 predicate {:opaque} ReEncryptCalledWith ( input: ReEncryptRequest ) {true}
 predicate {:opaque} ReEncryptSucceededWith (  input: ReEncryptRequest , output: ReEncryptResponse ) {true}
 predicate {:opaque} ReplicateKeyCalledWith ( input: ReplicateKeyRequest ) {true}
 predicate {:opaque} ReplicateKeySucceededWith (  input: ReplicateKeyRequest , output: ReplicateKeyResponse ) {true}
 predicate {:opaque} RetireGrantCalledWith ( input: RetireGrantRequest ) {true}
 predicate {:opaque} RetireGrantSucceededWith (  input: RetireGrantRequest ) {true}
 predicate {:opaque} RevokeGrantCalledWith ( input: RevokeGrantRequest ) {true}
 predicate {:opaque} RevokeGrantSucceededWith (  input: RevokeGrantRequest ) {true}
 predicate {:opaque} ScheduleKeyDeletionCalledWith ( input: ScheduleKeyDeletionRequest ) {true}
 predicate {:opaque} ScheduleKeyDeletionSucceededWith (  input: ScheduleKeyDeletionRequest , output: ScheduleKeyDeletionResponse ) {true}
 predicate {:opaque} SignCalledWith ( input: SignRequest ) {true}
 predicate {:opaque} SignSucceededWith (  input: SignRequest , output: SignResponse ) {true}
 predicate {:opaque} TagResourceCalledWith ( input: TagResourceRequest ) {true}
 predicate {:opaque} TagResourceSucceededWith (  input: TagResourceRequest ) {true}
 predicate {:opaque} UntagResourceCalledWith ( input: UntagResourceRequest ) {true}
 predicate {:opaque} UntagResourceSucceededWith (  input: UntagResourceRequest ) {true}
 predicate {:opaque} UpdateAliasCalledWith ( input: UpdateAliasRequest ) {true}
 predicate {:opaque} UpdateAliasSucceededWith (  input: UpdateAliasRequest ) {true}
 predicate {:opaque} UpdateCustomKeyStoreCalledWith ( input: UpdateCustomKeyStoreRequest ) {true}
 predicate {:opaque} UpdateCustomKeyStoreSucceededWith (  input: UpdateCustomKeyStoreRequest , output: UpdateCustomKeyStoreResponse ) {true}
 predicate {:opaque} UpdateKeyDescriptionCalledWith ( input: UpdateKeyDescriptionRequest ) {true}
 predicate {:opaque} UpdateKeyDescriptionSucceededWith (  input: UpdateKeyDescriptionRequest ) {true}
 predicate {:opaque} UpdatePrimaryRegionCalledWith ( input: UpdatePrimaryRegionRequest ) {true}
 predicate {:opaque} UpdatePrimaryRegionSucceededWith (  input: UpdatePrimaryRegionRequest ) {true}
 predicate {:opaque} VerifyCalledWith ( input: VerifyRequest ) {true}
 predicate {:opaque} VerifySucceededWith (  input: VerifyRequest , output: VerifyResponse ) {true}
 datatype KeyManagerType =
	| AWS
	| CUSTOMER
 datatype KeyMetadata = | KeyMetadata (
 nameonly AWSAccountId: Option<AWSAccountIdType> ,
 nameonly KeyId: KeyIdType ,
 nameonly Arn: Option<ArnType> ,
 nameonly CreationDate: Option<string> ,
 nameonly Enabled: Option<BooleanType> ,
 nameonly Description: Option<DescriptionType> ,
 nameonly KeyUsage: Option<KeyUsageType> ,
 nameonly KeyState: Option<KeyState> ,
 nameonly DeletionDate: Option<string> ,
 nameonly ValidTo: Option<string> ,
 nameonly Origin: Option<OriginType> ,
 nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> ,
 nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> ,
 nameonly ExpirationModel: Option<ExpirationModelType> ,
 nameonly KeyManager: Option<KeyManagerType> ,
 nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> ,
 nameonly KeySpec: Option<KeySpec> ,
 nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList> ,
 nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList> ,
 nameonly MultiRegion: Option<NullableBooleanType> ,
 nameonly MultiRegionConfiguration: Option<MultiRegionConfiguration> ,
 nameonly PendingDeletionWindowInDays: Option<PendingWindowInDaysType>
 )
 datatype KeySpec =
	| RSA_2048
	| RSA_3072
	| RSA_4096
	| ECC_NIST_P256
	| ECC_NIST_P384
	| ECC_NIST_P521
	| ECC_SECG_P256K1
	| SYMMETRIC_DEFAULT
 datatype KeyState =
	| Creating
	| Enabled
	| Disabled
	| PendingDeletion
	| PendingImport
	| PendingReplicaDeletion
	| Unavailable
	| Updating
 type KeyStorePasswordType = x: string | IsValid_KeyStorePasswordType(x) witness *
 predicate method IsValid_KeyStorePasswordType(x: string) {
 ( 7 <= |x| <= 32 )
}
 datatype KeyUsageType =
	| SIGN_VERIFY
	| ENCRYPT_DECRYPT
 type LimitType = x: int32 | IsValid_LimitType(x) witness *
 predicate method IsValid_LimitType(x: int32) {
 ( 1 <= x <= 1000 )
}
 datatype ListAliasesRequest = | ListAliasesRequest (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly Limit: Option<LimitType> ,
 nameonly Marker: Option<MarkerType>
 )
 datatype ListAliasesResponse = | ListAliasesResponse (
 nameonly Aliases: Option<AliasList> ,
 nameonly NextMarker: Option<MarkerType> ,
 nameonly Truncated: Option<BooleanType>
 )
 datatype ListGrantsRequest = | ListGrantsRequest (
 nameonly Limit: Option<LimitType> ,
 nameonly Marker: Option<MarkerType> ,
 nameonly KeyId: KeyIdType ,
 nameonly GrantId: Option<GrantIdType> ,
 nameonly GranteePrincipal: Option<PrincipalIdType>
 )
 datatype ListGrantsResponse = | ListGrantsResponse (
 nameonly Grants: Option<GrantList> ,
 nameonly NextMarker: Option<MarkerType> ,
 nameonly Truncated: Option<BooleanType>
 )
 datatype ListKeyPoliciesRequest = | ListKeyPoliciesRequest (
 nameonly KeyId: KeyIdType ,
 nameonly Limit: Option<LimitType> ,
 nameonly Marker: Option<MarkerType>
 )
 datatype ListKeyPoliciesResponse = | ListKeyPoliciesResponse (
 nameonly PolicyNames: Option<PolicyNameList> ,
 nameonly NextMarker: Option<MarkerType> ,
 nameonly Truncated: Option<BooleanType>
 )
 datatype ListKeysRequest = | ListKeysRequest (
 nameonly Limit: Option<LimitType> ,
 nameonly Marker: Option<MarkerType>
 )
 datatype ListResourceTagsRequest = | ListResourceTagsRequest (
 nameonly KeyId: KeyIdType ,
 nameonly Limit: Option<LimitType> ,
 nameonly Marker: Option<MarkerType>
 )
 datatype ListResourceTagsResponse = | ListResourceTagsResponse (
 nameonly Tags: Option<TagList> ,
 nameonly NextMarker: Option<MarkerType> ,
 nameonly Truncated: Option<BooleanType>
 )
 datatype ListRetirableGrantsRequest = | ListRetirableGrantsRequest (
 nameonly Limit: Option<LimitType> ,
 nameonly Marker: Option<MarkerType> ,
 nameonly RetiringPrincipal: PrincipalIdType
 )
 type MarkerType = x: string | IsValid_MarkerType(x) witness *
 predicate method IsValid_MarkerType(x: string) {
 ( 1 <= |x| <= 1024 )
}
 datatype MessageType =
	| RAW
	| DIGEST
 datatype MultiRegionConfiguration = | MultiRegionConfiguration (
 nameonly MultiRegionKeyType: Option<MultiRegionKeyType> ,
 nameonly PrimaryKey: Option<MultiRegionKey> ,
 nameonly ReplicaKeys: Option<MultiRegionKeyList>
 )
 datatype MultiRegionKey = | MultiRegionKey (
 nameonly Arn: Option<ArnType> ,
 nameonly Region: Option<RegionType>
 )
 type MultiRegionKeyList = seq<MultiRegionKey>
 datatype MultiRegionKeyType =
	| PRIMARY
	| REPLICA
 type NullableBooleanType = bool
 type NumberOfBytesType = x: int32 | IsValid_NumberOfBytesType(x) witness *
 predicate method IsValid_NumberOfBytesType(x: int32) {
 ( 1 <= x <= 1024 )
}
 datatype OriginType =
	| AWS_KMS
	| EXTERNAL
	| AWS_CLOUDHSM
 type PendingWindowInDaysType = x: int32 | IsValid_PendingWindowInDaysType(x) witness *
 predicate method IsValid_PendingWindowInDaysType(x: int32) {
 ( 1 <= x <= 365 )
}
 type PlaintextType = x: seq<uint8> | IsValid_PlaintextType(x) witness *
 predicate method IsValid_PlaintextType(x: seq<uint8>) {
 ( 1 <= |x| <= 4096 )
}
 type PolicyNameList = seq<PolicyNameType>
 type PolicyNameType = x: string | IsValid_PolicyNameType(x) witness *
 predicate method IsValid_PolicyNameType(x: string) {
 ( 1 <= |x| <= 128 )
}
 type PolicyType = x: string | IsValid_PolicyType(x) witness *
 predicate method IsValid_PolicyType(x: string) {
 ( 1 <= |x| <= 131072 )
}
 type PrincipalIdType = x: string | IsValid_PrincipalIdType(x) witness *
 predicate method IsValid_PrincipalIdType(x: string) {
 ( 1 <= |x| <= 256 )
}
 type PublicKeyType = x: seq<uint8> | IsValid_PublicKeyType(x) witness *
 predicate method IsValid_PublicKeyType(x: seq<uint8>) {
 ( 1 <= |x| <= 8192 )
}
 datatype PutKeyPolicyRequest = | PutKeyPolicyRequest (
 nameonly KeyId: KeyIdType ,
 nameonly PolicyName: PolicyNameType ,
 nameonly Policy: PolicyType ,
 nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType>
 )
 datatype ReEncryptRequest = | ReEncryptRequest (
 nameonly CiphertextBlob: CiphertextType ,
 nameonly SourceEncryptionContext: Option<EncryptionContextType> ,
 nameonly SourceKeyId: Option<KeyIdType> ,
 nameonly DestinationKeyId: KeyIdType ,
 nameonly DestinationEncryptionContext: Option<EncryptionContextType> ,
 nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> ,
 nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype ReEncryptResponse = | ReEncryptResponse (
 nameonly CiphertextBlob: Option<CiphertextType> ,
 nameonly SourceKeyId: Option<KeyIdType> ,
 nameonly KeyId: Option<KeyIdType> ,
 nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> ,
 nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>
 )
 type RegionType = x: string | IsValid_RegionType(x) witness *
 predicate method IsValid_RegionType(x: string) {
 ( 1 <= |x| <= 32 )
}
 datatype ReplicateKeyRequest = | ReplicateKeyRequest (
 nameonly KeyId: KeyIdType ,
 nameonly ReplicaRegion: RegionType ,
 nameonly Policy: Option<PolicyType> ,
 nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> ,
 nameonly Description: Option<DescriptionType> ,
 nameonly Tags: Option<TagList>
 )
 datatype ReplicateKeyResponse = | ReplicateKeyResponse (
 nameonly ReplicaKeyMetadata: Option<KeyMetadata> ,
 nameonly ReplicaPolicy: Option<PolicyType> ,
 nameonly ReplicaTags: Option<TagList>
 )
 datatype RetireGrantRequest = | RetireGrantRequest (
 nameonly GrantToken: Option<GrantTokenType> ,
 nameonly KeyId: Option<KeyIdType> ,
 nameonly GrantId: Option<GrantIdType>
 )
 datatype RevokeGrantRequest = | RevokeGrantRequest (
 nameonly KeyId: KeyIdType ,
 nameonly GrantId: GrantIdType
 )
 datatype ScheduleKeyDeletionRequest = | ScheduleKeyDeletionRequest (
 nameonly KeyId: KeyIdType ,
 nameonly PendingWindowInDays: Option<PendingWindowInDaysType>
 )
 datatype ScheduleKeyDeletionResponse = | ScheduleKeyDeletionResponse (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly DeletionDate: Option<string> ,
 nameonly KeyState: Option<KeyState> ,
 nameonly PendingWindowInDays: Option<PendingWindowInDaysType>
 )
 datatype SigningAlgorithmSpec =
	| RSASSA_PSS_SHA_256
	| RSASSA_PSS_SHA_384
	| RSASSA_PSS_SHA_512
	| RSASSA_PKCS1_V1_5_SHA_256
	| RSASSA_PKCS1_V1_5_SHA_384
	| RSASSA_PKCS1_V1_5_SHA_512
	| ECDSA_SHA_256
	| ECDSA_SHA_384
	| ECDSA_SHA_512
 type SigningAlgorithmSpecList = seq<SigningAlgorithmSpec>
 datatype SignRequest = | SignRequest (
 nameonly KeyId: KeyIdType ,
 nameonly Message: PlaintextType ,
 nameonly MessageType: Option<MessageType> ,
 nameonly GrantTokens: Option<GrantTokenList> ,
 nameonly SigningAlgorithm: SigningAlgorithmSpec
 )
 datatype SignResponse = | SignResponse (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly Signature: Option<CiphertextType> ,
 nameonly SigningAlgorithm: Option<SigningAlgorithmSpec>
 )
 datatype Tag = | Tag (
 nameonly TagKey: TagKeyType ,
 nameonly TagValue: TagValueType
 )
 type TagKeyList = seq<TagKeyType>
 type TagKeyType = x: string | IsValid_TagKeyType(x) witness *
 predicate method IsValid_TagKeyType(x: string) {
 ( 1 <= |x| <= 128 )
}
 type TagList = seq<Tag>
 datatype TagResourceRequest = | TagResourceRequest (
 nameonly KeyId: KeyIdType ,
 nameonly Tags: TagList
 )
 type TagValueType = x: string | IsValid_TagValueType(x) witness *
 predicate method IsValid_TagValueType(x: string) {
 ( 0 <= |x| <= 256 )
}
 type TrustAnchorCertificateType = x: string | IsValid_TrustAnchorCertificateType(x) witness *
 predicate method IsValid_TrustAnchorCertificateType(x: string) {
 ( 1 <= |x| <= 5000 )
}
 datatype UntagResourceRequest = | UntagResourceRequest (
 nameonly KeyId: KeyIdType ,
 nameonly TagKeys: TagKeyList
 )
 datatype UpdateAliasRequest = | UpdateAliasRequest (
 nameonly AliasName: AliasNameType ,
 nameonly TargetKeyId: KeyIdType
 )
 datatype UpdateCustomKeyStoreRequest = | UpdateCustomKeyStoreRequest (
 nameonly CustomKeyStoreId: CustomKeyStoreIdType ,
 nameonly NewCustomKeyStoreName: Option<CustomKeyStoreNameType> ,
 nameonly KeyStorePassword: Option<KeyStorePasswordType> ,
 nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType>
 )
 datatype UpdateCustomKeyStoreResponse = | UpdateCustomKeyStoreResponse (
 
 )
 datatype UpdateKeyDescriptionRequest = | UpdateKeyDescriptionRequest (
 nameonly KeyId: KeyIdType ,
 nameonly Description: DescriptionType
 )
 datatype UpdatePrimaryRegionRequest = | UpdatePrimaryRegionRequest (
 nameonly KeyId: KeyIdType ,
 nameonly PrimaryRegion: RegionType
 )
 datatype VerifyRequest = | VerifyRequest (
 nameonly KeyId: KeyIdType ,
 nameonly Message: PlaintextType ,
 nameonly MessageType: Option<MessageType> ,
 nameonly Signature: CiphertextType ,
 nameonly SigningAlgorithm: SigningAlgorithmSpec ,
 nameonly GrantTokens: Option<GrantTokenList>
 )
 datatype VerifyResponse = | VerifyResponse (
 nameonly KeyId: Option<KeyIdType> ,
 nameonly SignatureValid: Option<BooleanType> ,
 nameonly SigningAlgorithm: Option<SigningAlgorithmSpec>
 )
 datatype WrappingKeySpec =
	| RSA_2048
 datatype Error =
 // Local Error structures are listed here
 | CloudHsmClusterNotFoundException (
 nameonly message: Option<ErrorMessageType>
 )
 | CustomKeyStoreHasCMKsException (
 nameonly message: Option<ErrorMessageType>
 )
 | TagException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidImportTokenException (
 nameonly message: Option<ErrorMessageType>
 )
 | CloudHsmClusterNotRelatedException (
 nameonly message: Option<ErrorMessageType>
 )
 | DependencyTimeoutException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidGrantIdException (
 nameonly message: Option<ErrorMessageType>
 )
 | MalformedPolicyDocumentException (
 nameonly message: Option<ErrorMessageType>
 )
 | ExpiredImportTokenException (
 nameonly message: Option<ErrorMessageType>
 )
 | UnsupportedOperationException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidGrantTokenException (
 nameonly message: Option<ErrorMessageType>
 )
 | KeyUnavailableException (
 nameonly message: Option<ErrorMessageType>
 )
 | KMSInternalException (
 nameonly message: Option<ErrorMessageType>
 )
 | IncorrectKeyMaterialException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidCiphertextException (
 nameonly message: Option<ErrorMessageType>
 )
 | IncorrectTrustAnchorException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidMarkerException (
 nameonly message: Option<ErrorMessageType>
 )
 | LimitExceededException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidKeyUsageException (
 nameonly message: Option<ErrorMessageType>
 )
 | AlreadyExistsException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidArnException (
 nameonly message: Option<ErrorMessageType>
 )
 | CustomKeyStoreNotFoundException (
 nameonly message: Option<ErrorMessageType>
 )
 | InvalidAliasNameException (
 nameonly message: Option<ErrorMessageType>
 )
 | CloudHsmClusterInUseException (
 nameonly message: Option<ErrorMessageType>
 )
 | CloudHsmClusterInvalidConfigurationException (
 nameonly message: Option<ErrorMessageType>
 )
 | CustomKeyStoreNameInUseException (
 nameonly message: Option<ErrorMessageType>
 )
 | KMSInvalidSignatureException (
 nameonly message: Option<ErrorMessageType>
 )
 | KMSInvalidStateException (
 nameonly message: Option<ErrorMessageType>
 )
 | IncorrectKeyException (
 nameonly message: Option<ErrorMessageType>
 )
 | CloudHsmClusterNotActiveException (
 nameonly message: Option<ErrorMessageType>
 )
 | CustomKeyStoreInvalidStateException (
 nameonly message: Option<ErrorMessageType>
 )
 | DisabledException (
 nameonly message: Option<ErrorMessageType>
 )
 | NotFoundException (
 nameonly message: Option<ErrorMessageType>
 )
 // Any dependent models are listed here
 
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module ComAmazonawsKmsAbstract
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = ComAmazonawsKmsTypes
 datatype KMSClientConfigType = KMSClientConfigType
 function method DefaultKMSClientConfigType(): KMSClientConfigType
 class {:extern}  KMS extends IKeyManagementServiceClient
 {
 constructor {:extern} (config: KMSClientConfigType := DefaultKMSClientConfigType())
 method {:extern} CancelKeyDeletion
 ( input: CancelKeyDeletionRequest )
 returns (output: Result<CancelKeyDeletionResponse, Error>)
  ensures CancelKeyDeletionCalledWith (  input )
 ensures output.Success? ==> CancelKeyDeletionSucceededWith (  input , output.value )
 method {:extern} ConnectCustomKeyStore
 ( input: ConnectCustomKeyStoreRequest )
 returns (output: Result<ConnectCustomKeyStoreResponse, Error>)
  ensures ConnectCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> ConnectCustomKeyStoreSucceededWith (  input , output.value )
 method {:extern} CreateAlias
 ( input: CreateAliasRequest )
 returns (output: Result<(), Error>)
  ensures CreateAliasCalledWith (  input )
 ensures output.Success? ==> CreateAliasSucceededWith (  input )
 method {:extern} CreateCustomKeyStore
 ( input: CreateCustomKeyStoreRequest )
 returns (output: Result<CreateCustomKeyStoreResponse, Error>)
  ensures CreateCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> CreateCustomKeyStoreSucceededWith (  input , output.value )
 method {:extern} CreateGrant
 ( input: CreateGrantRequest )
 returns (output: Result<CreateGrantResponse, Error>)
  ensures CreateGrantCalledWith (  input )
 ensures output.Success? ==> CreateGrantSucceededWith (  input , output.value )
 method {:extern} CreateKey
 ( input: CreateKeyRequest )
 returns (output: Result<CreateKeyResponse, Error>)
  ensures CreateKeyCalledWith (  input )
 ensures output.Success? ==> CreateKeySucceededWith (  input , output.value )
 method {:extern} Decrypt
 ( input: DecryptRequest )
 returns (output: Result<DecryptResponse, Error>)
  ensures DecryptCalledWith (  input )
 ensures output.Success? ==> DecryptSucceededWith (  input , output.value )
 method {:extern} DeleteAlias
 ( input: DeleteAliasRequest )
 returns (output: Result<(), Error>)
  ensures DeleteAliasCalledWith (  input )
 ensures output.Success? ==> DeleteAliasSucceededWith (  input )
 method {:extern} DeleteCustomKeyStore
 ( input: DeleteCustomKeyStoreRequest )
 returns (output: Result<DeleteCustomKeyStoreResponse, Error>)
  ensures DeleteCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> DeleteCustomKeyStoreSucceededWith (  input , output.value )
 method {:extern} DeleteImportedKeyMaterial
 ( input: DeleteImportedKeyMaterialRequest )
 returns (output: Result<(), Error>)
  ensures DeleteImportedKeyMaterialCalledWith (  input )
 ensures output.Success? ==> DeleteImportedKeyMaterialSucceededWith (  input )
 method {:extern} DescribeCustomKeyStores
 ( input: DescribeCustomKeyStoresRequest )
 returns (output: Result<DescribeCustomKeyStoresResponse, Error>)
  ensures DescribeCustomKeyStoresCalledWith (  input )
 ensures output.Success? ==> DescribeCustomKeyStoresSucceededWith (  input , output.value )
 method {:extern} DescribeKey
 ( input: DescribeKeyRequest )
 returns (output: Result<DescribeKeyResponse, Error>)
  ensures DescribeKeyCalledWith (  input )
 ensures output.Success? ==> DescribeKeySucceededWith (  input , output.value )
 method {:extern} DisableKey
 ( input: DisableKeyRequest )
 returns (output: Result<(), Error>)
  ensures DisableKeyCalledWith (  input )
 ensures output.Success? ==> DisableKeySucceededWith (  input )
 method {:extern} DisableKeyRotation
 ( input: DisableKeyRotationRequest )
 returns (output: Result<(), Error>)
  ensures DisableKeyRotationCalledWith (  input )
 ensures output.Success? ==> DisableKeyRotationSucceededWith (  input )
 method {:extern} DisconnectCustomKeyStore
 ( input: DisconnectCustomKeyStoreRequest )
 returns (output: Result<DisconnectCustomKeyStoreResponse, Error>)
  ensures DisconnectCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> DisconnectCustomKeyStoreSucceededWith (  input , output.value )
 method {:extern} EnableKey
 ( input: EnableKeyRequest )
 returns (output: Result<(), Error>)
  ensures EnableKeyCalledWith (  input )
 ensures output.Success? ==> EnableKeySucceededWith (  input )
 method {:extern} EnableKeyRotation
 ( input: EnableKeyRotationRequest )
 returns (output: Result<(), Error>)
  ensures EnableKeyRotationCalledWith (  input )
 ensures output.Success? ==> EnableKeyRotationSucceededWith (  input )
 method {:extern} Encrypt
 ( input: EncryptRequest )
 returns (output: Result<EncryptResponse, Error>)
  ensures EncryptCalledWith (  input )
 ensures output.Success? ==> EncryptSucceededWith (  input , output.value )
 method {:extern} GenerateDataKey
 ( input: GenerateDataKeyRequest )
 returns (output: Result<GenerateDataKeyResponse, Error>)
  ensures GenerateDataKeyCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeySucceededWith (  input , output.value )
 method {:extern} GenerateDataKeyPair
 ( input: GenerateDataKeyPairRequest )
 returns (output: Result<GenerateDataKeyPairResponse, Error>)
  ensures GenerateDataKeyPairCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeyPairSucceededWith (  input , output.value )
 method {:extern} GenerateDataKeyPairWithoutPlaintext
 ( input: GenerateDataKeyPairWithoutPlaintextRequest )
 returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
  ensures GenerateDataKeyPairWithoutPlaintextCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeyPairWithoutPlaintextSucceededWith (  input , output.value )
 method {:extern} GenerateDataKeyWithoutPlaintext
 ( input: GenerateDataKeyWithoutPlaintextRequest )
 returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
  ensures GenerateDataKeyWithoutPlaintextCalledWith (  input )
 ensures output.Success? ==> GenerateDataKeyWithoutPlaintextSucceededWith (  input , output.value )
 method {:extern} GenerateRandom
 ( input: GenerateRandomRequest )
 returns (output: Result<GenerateRandomResponse, Error>)
  ensures GenerateRandomCalledWith (  input )
 ensures output.Success? ==> GenerateRandomSucceededWith (  input , output.value )
 method {:extern} GetKeyPolicy
 ( input: GetKeyPolicyRequest )
 returns (output: Result<GetKeyPolicyResponse, Error>)
  ensures GetKeyPolicyCalledWith (  input )
 ensures output.Success? ==> GetKeyPolicySucceededWith (  input , output.value )
 method {:extern} GetKeyRotationStatus
 ( input: GetKeyRotationStatusRequest )
 returns (output: Result<GetKeyRotationStatusResponse, Error>)
  ensures GetKeyRotationStatusCalledWith (  input )
 ensures output.Success? ==> GetKeyRotationStatusSucceededWith (  input , output.value )
 method {:extern} GetParametersForImport
 ( input: GetParametersForImportRequest )
 returns (output: Result<GetParametersForImportResponse, Error>)
  ensures GetParametersForImportCalledWith (  input )
 ensures output.Success? ==> GetParametersForImportSucceededWith (  input , output.value )
 method {:extern} GetPublicKey
 ( input: GetPublicKeyRequest )
 returns (output: Result<GetPublicKeyResponse, Error>)
  ensures GetPublicKeyCalledWith (  input )
 ensures output.Success? ==> GetPublicKeySucceededWith (  input , output.value )
 method {:extern} ImportKeyMaterial
 ( input: ImportKeyMaterialRequest )
 returns (output: Result<ImportKeyMaterialResponse, Error>)
  ensures ImportKeyMaterialCalledWith (  input )
 ensures output.Success? ==> ImportKeyMaterialSucceededWith (  input , output.value )
 method {:extern} ListAliases
 ( input: ListAliasesRequest )
 returns (output: Result<ListAliasesResponse, Error>)
  ensures ListAliasesCalledWith (  input )
 ensures output.Success? ==> ListAliasesSucceededWith (  input , output.value )
 method {:extern} ListGrants
 ( input: ListGrantsRequest )
 returns (output: Result<ListGrantsResponse, Error>)
  ensures ListGrantsCalledWith (  input )
 ensures output.Success? ==> ListGrantsSucceededWith (  input , output.value )
 method {:extern} ListKeyPolicies
 ( input: ListKeyPoliciesRequest )
 returns (output: Result<ListKeyPoliciesResponse, Error>)
  ensures ListKeyPoliciesCalledWith (  input )
 ensures output.Success? ==> ListKeyPoliciesSucceededWith (  input , output.value )
 method {:extern} ListResourceTags
 ( input: ListResourceTagsRequest )
 returns (output: Result<ListResourceTagsResponse, Error>)
  ensures ListResourceTagsCalledWith (  input )
 ensures output.Success? ==> ListResourceTagsSucceededWith (  input , output.value )
 method {:extern} PutKeyPolicy
 ( input: PutKeyPolicyRequest )
 returns (output: Result<(), Error>)
  ensures PutKeyPolicyCalledWith (  input )
 ensures output.Success? ==> PutKeyPolicySucceededWith (  input )
 method {:extern} ReEncrypt
 ( input: ReEncryptRequest )
 returns (output: Result<ReEncryptResponse, Error>)
  ensures ReEncryptCalledWith (  input )
 ensures output.Success? ==> ReEncryptSucceededWith (  input , output.value )
 method {:extern} ReplicateKey
 ( input: ReplicateKeyRequest )
 returns (output: Result<ReplicateKeyResponse, Error>)
  ensures ReplicateKeyCalledWith (  input )
 ensures output.Success? ==> ReplicateKeySucceededWith (  input , output.value )
 method {:extern} RetireGrant
 ( input: RetireGrantRequest )
 returns (output: Result<(), Error>)
  ensures RetireGrantCalledWith (  input )
 ensures output.Success? ==> RetireGrantSucceededWith (  input )
 method {:extern} RevokeGrant
 ( input: RevokeGrantRequest )
 returns (output: Result<(), Error>)
  ensures RevokeGrantCalledWith (  input )
 ensures output.Success? ==> RevokeGrantSucceededWith (  input )
 method {:extern} ScheduleKeyDeletion
 ( input: ScheduleKeyDeletionRequest )
 returns (output: Result<ScheduleKeyDeletionResponse, Error>)
  ensures ScheduleKeyDeletionCalledWith (  input )
 ensures output.Success? ==> ScheduleKeyDeletionSucceededWith (  input , output.value )
 method {:extern} Sign
 ( input: SignRequest )
 returns (output: Result<SignResponse, Error>)
  ensures SignCalledWith (  input )
 ensures output.Success? ==> SignSucceededWith (  input , output.value )
 method {:extern} TagResource
 ( input: TagResourceRequest )
 returns (output: Result<(), Error>)
  ensures TagResourceCalledWith (  input )
 ensures output.Success? ==> TagResourceSucceededWith (  input )
 method {:extern} UntagResource
 ( input: UntagResourceRequest )
 returns (output: Result<(), Error>)
  ensures UntagResourceCalledWith (  input )
 ensures output.Success? ==> UntagResourceSucceededWith (  input )
 method {:extern} UpdateAlias
 ( input: UpdateAliasRequest )
 returns (output: Result<(), Error>)
  ensures UpdateAliasCalledWith (  input )
 ensures output.Success? ==> UpdateAliasSucceededWith (  input )
 method {:extern} UpdateCustomKeyStore
 ( input: UpdateCustomKeyStoreRequest )
 returns (output: Result<UpdateCustomKeyStoreResponse, Error>)
  ensures UpdateCustomKeyStoreCalledWith (  input )
 ensures output.Success? ==> UpdateCustomKeyStoreSucceededWith (  input , output.value )
 method {:extern} UpdateKeyDescription
 ( input: UpdateKeyDescriptionRequest )
 returns (output: Result<(), Error>)
  ensures UpdateKeyDescriptionCalledWith (  input )
 ensures output.Success? ==> UpdateKeyDescriptionSucceededWith (  input )
 method {:extern} UpdatePrimaryRegion
 ( input: UpdatePrimaryRegionRequest )
 returns (output: Result<(), Error>)
  ensures UpdatePrimaryRegionCalledWith (  input )
 ensures output.Success? ==> UpdatePrimaryRegionSucceededWith (  input )
 method {:extern} Verify
 ( input: VerifyRequest )
 returns (output: Result<VerifyResponse, Error>)
  ensures VerifyCalledWith (  input )
 ensures output.Success? ==> VerifySucceededWith (  input , output.value )
}
}
