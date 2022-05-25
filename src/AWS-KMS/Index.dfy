// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "Model/ComAmazonawsKmsTypes.dfy"

module Com.Amazonaws.Kms {
  import opened Wrappers
  import opened Types = ComAmazonawsKmsTypes

  class {:extern "KMS"} KMS extends IKeyManagementServiceClient {

 method {:extern "CancelKeyDeletion"} CancelKeyDeletion ( input: CancelKeyDeletionRequest ) returns  ( output: Result<CancelKeyDeletionResponse, Error> )
	ensures CancelKeyDeletionCalledWith (  input )
	ensures output.Success? ==> CancelKeyDeletionSucceededWith (  input , output.value )

 method {:extern "ConnectCustomKeyStore"} ConnectCustomKeyStore ( input: ConnectCustomKeyStoreRequest ) returns  ( output: Result<ConnectCustomKeyStoreResponse, Error> )
	ensures ConnectCustomKeyStoreCalledWith (  input )
	ensures output.Success? ==> ConnectCustomKeyStoreSucceededWith (  input , output.value )

 method {:extern "CreateAlias"} CreateAlias ( input: CreateAliasRequest ) returns  ( output: Result<(), Error> )
	ensures CreateAliasCalledWith (  input )
	ensures output.Success? ==> CreateAliasSucceededWith (  input )

 method {:extern "CreateCustomKeyStore"} CreateCustomKeyStore ( input: CreateCustomKeyStoreRequest ) returns  ( output: Result<CreateCustomKeyStoreResponse, Error> )
	ensures CreateCustomKeyStoreCalledWith (  input )
	ensures output.Success? ==> CreateCustomKeyStoreSucceededWith (  input , output.value )

 method {:extern "CreateGrant"} CreateGrant ( input: CreateGrantRequest ) returns  ( output: Result<CreateGrantResponse, Error> )
	ensures CreateGrantCalledWith (  input )
	ensures output.Success? ==> CreateGrantSucceededWith (  input , output.value )

 method {:extern "CreateKey"} CreateKey ( input: CreateKeyRequest ) returns  ( output: Result<CreateKeyResponse, Error> )
	ensures CreateKeyCalledWith (  input )
	ensures output.Success? ==> CreateKeySucceededWith (  input , output.value )

 method {:extern "Decrypt"} Decrypt ( input: DecryptRequest ) returns  ( output: Result<DecryptResponse, Error> )
	ensures DecryptCalledWith (  input )
	ensures output.Success? ==> DecryptSucceededWith (  input , output.value )

 method {:extern "DeleteAlias"} DeleteAlias ( input: DeleteAliasRequest ) returns  ( output: Result<(), Error> )
	ensures DeleteAliasCalledWith (  input )
	ensures output.Success? ==> DeleteAliasSucceededWith (  input )

 method {:extern "DeleteCustomKeyStore"} DeleteCustomKeyStore ( input: DeleteCustomKeyStoreRequest ) returns  ( output: Result<DeleteCustomKeyStoreResponse, Error> )
	ensures DeleteCustomKeyStoreCalledWith (  input )
	ensures output.Success? ==> DeleteCustomKeyStoreSucceededWith (  input , output.value )

 method {:extern "DeleteImportedKeyMaterial"} DeleteImportedKeyMaterial ( input: DeleteImportedKeyMaterialRequest ) returns  ( output: Result<(), Error> )
	ensures DeleteImportedKeyMaterialCalledWith (  input )
	ensures output.Success? ==> DeleteImportedKeyMaterialSucceededWith (  input )

 method {:extern "DescribeCustomKeyStores"} DescribeCustomKeyStores ( input: DescribeCustomKeyStoresRequest ) returns  ( output: Result<DescribeCustomKeyStoresResponse, Error> )
	ensures DescribeCustomKeyStoresCalledWith (  input )
	ensures output.Success? ==> DescribeCustomKeyStoresSucceededWith (  input , output.value )

 method {:extern "DescribeKey"} DescribeKey ( input: DescribeKeyRequest ) returns  ( output: Result<DescribeKeyResponse, Error> )
	ensures DescribeKeyCalledWith (  input )
	ensures output.Success? ==> DescribeKeySucceededWith (  input , output.value )

 method {:extern "DisableKey"} DisableKey ( input: DisableKeyRequest ) returns  ( output: Result<(), Error> )
	ensures DisableKeyCalledWith (  input )
	ensures output.Success? ==> DisableKeySucceededWith (  input )

 method {:extern "DisableKeyRotation"} DisableKeyRotation ( input: DisableKeyRotationRequest ) returns  ( output: Result<(), Error> )
	ensures DisableKeyRotationCalledWith (  input )
	ensures output.Success? ==> DisableKeyRotationSucceededWith (  input )

 method {:extern "DisconnectCustomKeyStore"} DisconnectCustomKeyStore ( input: DisconnectCustomKeyStoreRequest ) returns  ( output: Result<DisconnectCustomKeyStoreResponse, Error> )
	ensures DisconnectCustomKeyStoreCalledWith (  input )
	ensures output.Success? ==> DisconnectCustomKeyStoreSucceededWith (  input , output.value )

 method {:extern "EnableKey"} EnableKey ( input: EnableKeyRequest ) returns  ( output: Result<(), Error> )
	ensures EnableKeyCalledWith (  input )
	ensures output.Success? ==> EnableKeySucceededWith (  input )

 method {:extern "EnableKeyRotation"} EnableKeyRotation ( input: EnableKeyRotationRequest ) returns  ( output: Result<(), Error> )
	ensures EnableKeyRotationCalledWith (  input )
	ensures output.Success? ==> EnableKeyRotationSucceededWith (  input )

 method {:extern "Encrypt"} Encrypt ( input: EncryptRequest ) returns  ( output: Result<EncryptResponse, Error> )
	ensures EncryptCalledWith (  input )
	ensures output.Success? ==> EncryptSucceededWith (  input , output.value )

 method {:extern "GenerateDataKey"} GenerateDataKey ( input: GenerateDataKeyRequest ) returns  ( output: Result<GenerateDataKeyResponse, Error> )
	ensures GenerateDataKeyCalledWith (  input )
	ensures output.Success? ==> GenerateDataKeySucceededWith (  input , output.value )

 method {:extern "GenerateDataKeyPair"} GenerateDataKeyPair ( input: GenerateDataKeyPairRequest ) returns  ( output: Result<GenerateDataKeyPairResponse, Error> )
	ensures GenerateDataKeyPairCalledWith (  input )
	ensures output.Success? ==> GenerateDataKeyPairSucceededWith (  input , output.value )

 method {:extern "GenerateDataKeyPairWithoutPlaintext"} GenerateDataKeyPairWithoutPlaintext ( input: GenerateDataKeyPairWithoutPlaintextRequest ) returns  ( output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error> )
	ensures GenerateDataKeyPairWithoutPlaintextCalledWith (  input )
	ensures output.Success? ==> GenerateDataKeyPairWithoutPlaintextSucceededWith (  input , output.value )

 method {:extern "GenerateDataKeyWithoutPlaintext"} GenerateDataKeyWithoutPlaintext ( input: GenerateDataKeyWithoutPlaintextRequest ) returns  ( output: Result<GenerateDataKeyWithoutPlaintextResponse, Error> )
	ensures GenerateDataKeyWithoutPlaintextCalledWith (  input )
	ensures output.Success? ==> GenerateDataKeyWithoutPlaintextSucceededWith (  input , output.value )

 method {:extern "GenerateRandom"} GenerateRandom ( input: GenerateRandomRequest ) returns  ( output: Result<GenerateRandomResponse, Error> )
	ensures GenerateRandomCalledWith (  input )
	ensures output.Success? ==> GenerateRandomSucceededWith (  input , output.value )

 method {:extern "GetKeyPolicy"} GetKeyPolicy ( input: GetKeyPolicyRequest ) returns  ( output: Result<GetKeyPolicyResponse, Error> )
	ensures GetKeyPolicyCalledWith (  input )
	ensures output.Success? ==> GetKeyPolicySucceededWith (  input , output.value )

 method {:extern "GetKeyRotationStatus"} GetKeyRotationStatus ( input: GetKeyRotationStatusRequest ) returns  ( output: Result<GetKeyRotationStatusResponse, Error> )
	ensures GetKeyRotationStatusCalledWith (  input )
	ensures output.Success? ==> GetKeyRotationStatusSucceededWith (  input , output.value )

 method {:extern "GetParametersForImport"} GetParametersForImport ( input: GetParametersForImportRequest ) returns  ( output: Result<GetParametersForImportResponse, Error> )
	ensures GetParametersForImportCalledWith (  input )
	ensures output.Success? ==> GetParametersForImportSucceededWith (  input , output.value )

 method {:extern "GetPublicKey"} GetPublicKey ( input: GetPublicKeyRequest ) returns  ( output: Result<GetPublicKeyResponse, Error> )
	ensures GetPublicKeyCalledWith (  input )
	ensures output.Success? ==> GetPublicKeySucceededWith (  input , output.value )

 method {:extern "ImportKeyMaterial"} ImportKeyMaterial ( input: ImportKeyMaterialRequest ) returns  ( output: Result<ImportKeyMaterialResponse, Error> )
	ensures ImportKeyMaterialCalledWith (  input )
	ensures output.Success? ==> ImportKeyMaterialSucceededWith (  input , output.value )

 method {:extern "ListAliases"} ListAliases ( input: ListAliasesRequest ) returns  ( output: Result<ListAliasesResponse, Error> )
	ensures ListAliasesCalledWith (  input )
	ensures output.Success? ==> ListAliasesSucceededWith (  input , output.value )

 method {:extern "ListGrants"} ListGrants ( input: ListGrantsRequest ) returns  ( output: Result<ListGrantsResponse, Error> )
	ensures ListGrantsCalledWith (  input )
	ensures output.Success? ==> ListGrantsSucceededWith (  input , output.value )

 method {:extern "ListKeyPolicies"} ListKeyPolicies ( input: ListKeyPoliciesRequest ) returns  ( output: Result<ListKeyPoliciesResponse, Error> )
	ensures ListKeyPoliciesCalledWith (  input )
	ensures output.Success? ==> ListKeyPoliciesSucceededWith (  input , output.value )

 method {:extern "ListResourceTags"} ListResourceTags ( input: ListResourceTagsRequest ) returns  ( output: Result<ListResourceTagsResponse, Error> )
	ensures ListResourceTagsCalledWith (  input )
	ensures output.Success? ==> ListResourceTagsSucceededWith (  input , output.value )

 method {:extern "PutKeyPolicy"} PutKeyPolicy ( input: PutKeyPolicyRequest ) returns  ( output: Result<(), Error> )
	ensures PutKeyPolicyCalledWith (  input )
	ensures output.Success? ==> PutKeyPolicySucceededWith (  input )

 method {:extern "ReEncrypt"} ReEncrypt ( input: ReEncryptRequest ) returns  ( output: Result<ReEncryptResponse, Error> )
	ensures ReEncryptCalledWith (  input )
	ensures output.Success? ==> ReEncryptSucceededWith (  input , output.value )

 method {:extern "ReplicateKey"} ReplicateKey ( input: ReplicateKeyRequest ) returns  ( output: Result<ReplicateKeyResponse, Error> )
	ensures ReplicateKeyCalledWith (  input )
	ensures output.Success? ==> ReplicateKeySucceededWith (  input , output.value )

 method {:extern "RetireGrant"} RetireGrant ( input: RetireGrantRequest ) returns  ( output: Result<(), Error> )
	ensures RetireGrantCalledWith (  input )
	ensures output.Success? ==> RetireGrantSucceededWith (  input )

 method {:extern "RevokeGrant"} RevokeGrant ( input: RevokeGrantRequest ) returns  ( output: Result<(), Error> )
	ensures RevokeGrantCalledWith (  input )
	ensures output.Success? ==> RevokeGrantSucceededWith (  input )

 method {:extern "ScheduleKeyDeletion"} ScheduleKeyDeletion ( input: ScheduleKeyDeletionRequest ) returns  ( output: Result<ScheduleKeyDeletionResponse, Error> )
	ensures ScheduleKeyDeletionCalledWith (  input )
	ensures output.Success? ==> ScheduleKeyDeletionSucceededWith (  input , output.value )

 method {:extern "Sign"} Sign ( input: SignRequest ) returns  ( output: Result<SignResponse, Error> )
	ensures SignCalledWith (  input )
	ensures output.Success? ==> SignSucceededWith (  input , output.value )

 method {:extern "TagResource"} TagResource ( input: TagResourceRequest ) returns  ( output: Result<(), Error> )
	ensures TagResourceCalledWith (  input )
	ensures output.Success? ==> TagResourceSucceededWith (  input )

 method {:extern "UntagResource"} UntagResource ( input: UntagResourceRequest ) returns  ( output: Result<(), Error> )
	ensures UntagResourceCalledWith (  input )
	ensures output.Success? ==> UntagResourceSucceededWith (  input )

 method {:extern "UpdateAlias"} UpdateAlias ( input: UpdateAliasRequest ) returns  ( output: Result<(), Error> )
	ensures UpdateAliasCalledWith (  input )
	ensures output.Success? ==> UpdateAliasSucceededWith (  input )

 method {:extern "UpdateCustomKeyStore"} UpdateCustomKeyStore ( input: UpdateCustomKeyStoreRequest ) returns  ( output: Result<UpdateCustomKeyStoreResponse, Error> )
	ensures UpdateCustomKeyStoreCalledWith (  input )
	ensures output.Success? ==> UpdateCustomKeyStoreSucceededWith (  input , output.value )

 method {:extern "UpdateKeyDescription"} UpdateKeyDescription ( input: UpdateKeyDescriptionRequest ) returns  ( output: Result<(), Error> )
	ensures UpdateKeyDescriptionCalledWith (  input )
	ensures output.Success? ==> UpdateKeyDescriptionSucceededWith (  input )

 method {:extern "UpdatePrimaryRegion"} UpdatePrimaryRegion ( input: UpdatePrimaryRegionRequest ) returns  ( output: Result<(), Error> )
	ensures UpdatePrimaryRegionCalledWith (  input )
	ensures output.Success? ==> UpdatePrimaryRegionSucceededWith (  input )

 method {:extern "Verify"} Verify ( input: VerifyRequest ) returns  ( output: Result<VerifyResponse, Error> )
	ensures VerifyCalledWith (  input )
	ensures output.Success? ==> VerifySucceededWith (  input , output.value )

  }
}