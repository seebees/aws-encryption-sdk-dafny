// Dafny program Index.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.6.0.40511
// Command Line Options: /compileTarget:cs /spillTargetCode:3 /compile:0 /noVerify /out runtimes/net/Source/FromDafny src/Index.dfy
// Index.dfy


module ComAmazonawsKmsTypes {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8
  datatype AlgorithmSpec = RSAES_PKCS1_V1_5 | RSAES_OAEP_SHA_1 | RSAES_OAEP_SHA_256

  type AliasList = seq<AliasListEntry>

  datatype AliasListEntry = AliasListEntry(nameonly AliasName: Option<AliasNameType>, nameonly AliasArn: Option<ArnType>, nameonly TargetKeyId: Option<KeyIdType>, nameonly CreationDate: Option<string>, nameonly LastUpdatedDate: Option<string>)

  type AliasNameType = x: string
    | IsValid_AliasNameType(x)
    witness *

  type ArnType = x: string
    | IsValid_ArnType(x)
    witness *

  type AWSAccountIdType = string

  type BooleanType = bool

  datatype CancelKeyDeletionRequest = CancelKeyDeletionRequest(nameonly KeyId: KeyIdType)

  datatype CancelKeyDeletionResponse = CancelKeyDeletionResponse(nameonly KeyId: Option<KeyIdType>)

  type CiphertextType = x: seq<uint8>
    | IsValid_CiphertextType(x)
    witness *

  type CloudHsmClusterIdType = x: string
    | IsValid_CloudHsmClusterIdType(x)
    witness *

  datatype ConnectCustomKeyStoreRequest = ConnectCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType)

  datatype ConnectCustomKeyStoreResponse = ConnectCustomKeyStoreResponse

  datatype ConnectionErrorCodeType = INVALID_CREDENTIALS | CLUSTER_NOT_FOUND | NETWORK_ERRORS | INTERNAL_ERROR | INSUFFICIENT_CLOUDHSM_HSMS | USER_LOCKED_OUT | USER_NOT_FOUND | USER_LOGGED_IN | SUBNET_NOT_FOUND

  datatype ConnectionStateType = CONNECTED | CONNECTING | FAILED | DISCONNECTED | DISCONNECTING

  datatype CreateAliasRequest = CreateAliasRequest(nameonly AliasName: AliasNameType, nameonly TargetKeyId: KeyIdType)

  datatype CreateCustomKeyStoreRequest = CreateCustomKeyStoreRequest(nameonly CustomKeyStoreName: CustomKeyStoreNameType, nameonly CloudHsmClusterId: CloudHsmClusterIdType, nameonly TrustAnchorCertificate: TrustAnchorCertificateType, nameonly KeyStorePassword: KeyStorePasswordType)

  datatype CreateCustomKeyStoreResponse = CreateCustomKeyStoreResponse(nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>)

  datatype CreateGrantRequest = CreateGrantRequest(nameonly KeyId: KeyIdType, nameonly GranteePrincipal: PrincipalIdType, nameonly RetiringPrincipal: Option<PrincipalIdType>, nameonly Operations: GrantOperationList, nameonly Constraints: Option<GrantConstraints>, nameonly GrantTokens: Option<GrantTokenList>, nameonly Name: Option<GrantNameType>)

  datatype CreateGrantResponse = CreateGrantResponse(nameonly GrantToken: Option<GrantTokenType>, nameonly GrantId: Option<GrantIdType>)

  datatype CreateKeyRequest = CreateKeyRequest(nameonly Policy: Option<PolicyType>, nameonly Description: Option<DescriptionType>, nameonly KeyUsage: Option<KeyUsageType>, nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec>, nameonly KeySpec: Option<KeySpec>, nameonly Origin: Option<OriginType>, nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType>, nameonly Tags: Option<TagList>, nameonly MultiRegion: Option<NullableBooleanType>)

  datatype CreateKeyResponse = CreateKeyResponse(nameonly KeyMetadata: Option<KeyMetadata>)

  datatype CustomerMasterKeySpec = RSA_2048 | RSA_3072 | RSA_4096 | ECC_NIST_P256 | ECC_NIST_P384 | ECC_NIST_P521 | ECC_SECG_P256K1 | SYMMETRIC_DEFAULT

  type CustomKeyStoreIdType = x: string
    | IsValid_CustomKeyStoreIdType(x)
    witness *

  type CustomKeyStoreNameType = x: string
    | IsValid_CustomKeyStoreNameType(x)
    witness *

  type CustomKeyStoresList = seq<CustomKeyStoresListEntry>

  datatype CustomKeyStoresListEntry = CustomKeyStoresListEntry(nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType>, nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType>, nameonly TrustAnchorCertificate: Option<TrustAnchorCertificateType>, nameonly ConnectionState: Option<ConnectionStateType>, nameonly ConnectionErrorCode: Option<ConnectionErrorCodeType>, nameonly CreationDate: Option<string>)

  datatype DataKeyPairSpec = RSA_2048 | RSA_3072 | RSA_4096 | ECC_NIST_P256 | ECC_NIST_P384 | ECC_NIST_P521 | ECC_SECG_P256K1

  datatype DataKeySpec = AES_256 | AES_128

  datatype DecryptRequest = DecryptRequest(nameonly CiphertextBlob: CiphertextType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly GrantTokens: Option<GrantTokenList>, nameonly KeyId: Option<KeyIdType>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  datatype DecryptResponse = DecryptResponse(nameonly KeyId: Option<KeyIdType>, nameonly Plaintext: Option<PlaintextType>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  datatype DeleteAliasRequest = DeleteAliasRequest(nameonly AliasName: AliasNameType)

  datatype DeleteCustomKeyStoreRequest = DeleteCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType)

  datatype DeleteCustomKeyStoreResponse = DeleteCustomKeyStoreResponse

  datatype DeleteImportedKeyMaterialRequest = DeleteImportedKeyMaterialRequest(nameonly KeyId: KeyIdType)

  datatype DescribeCustomKeyStoresRequest = DescribeCustomKeyStoresRequest(nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType>, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype DescribeCustomKeyStoresResponse = DescribeCustomKeyStoresResponse(nameonly CustomKeyStores: Option<CustomKeyStoresList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype DescribeKeyRequest = DescribeKeyRequest(nameonly KeyId: KeyIdType, nameonly GrantTokens: Option<GrantTokenList>)

  datatype DescribeKeyResponse = DescribeKeyResponse(nameonly KeyMetadata: Option<KeyMetadata>)

  type DescriptionType = x: string
    | IsValid_DescriptionType(x)
    witness *

  datatype DisableKeyRequest = DisableKeyRequest(nameonly KeyId: KeyIdType)

  datatype DisableKeyRotationRequest = DisableKeyRotationRequest(nameonly KeyId: KeyIdType)

  datatype DisconnectCustomKeyStoreRequest = DisconnectCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType)

  datatype DisconnectCustomKeyStoreResponse = DisconnectCustomKeyStoreResponse

  datatype EnableKeyRequest = EnableKeyRequest(nameonly KeyId: KeyIdType)

  datatype EnableKeyRotationRequest = EnableKeyRotationRequest(nameonly KeyId: KeyIdType)

  datatype EncryptionAlgorithmSpec = SYMMETRIC_DEFAULT | RSAES_OAEP_SHA_1 | RSAES_OAEP_SHA_256

  type EncryptionAlgorithmSpecList = seq<EncryptionAlgorithmSpec>

  type EncryptionContextKey = string

  type EncryptionContextType = map<EncryptionContextKey, EncryptionContextValue>

  type EncryptionContextValue = string

  datatype EncryptRequest = EncryptRequest(nameonly KeyId: KeyIdType, nameonly Plaintext: PlaintextType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly GrantTokens: Option<GrantTokenList>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  datatype EncryptResponse = EncryptResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly KeyId: Option<KeyIdType>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  type ErrorMessageType = string

  datatype ExpirationModelType = KEY_MATERIAL_EXPIRES | KEY_MATERIAL_DOES_NOT_EXPIRE

  datatype GenerateDataKeyPairRequest = GenerateDataKeyPairRequest(nameonly EncryptionContext: Option<EncryptionContextType>, nameonly KeyId: KeyIdType, nameonly KeyPairSpec: DataKeyPairSpec, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyPairResponse = GenerateDataKeyPairResponse(nameonly PrivateKeyCiphertextBlob: Option<CiphertextType>, nameonly PrivateKeyPlaintext: Option<PlaintextType>, nameonly PublicKey: Option<PublicKeyType>, nameonly KeyId: Option<KeyIdType>, nameonly KeyPairSpec: Option<DataKeyPairSpec>)

  datatype GenerateDataKeyPairWithoutPlaintextRequest = GenerateDataKeyPairWithoutPlaintextRequest(nameonly EncryptionContext: Option<EncryptionContextType>, nameonly KeyId: KeyIdType, nameonly KeyPairSpec: DataKeyPairSpec, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyPairWithoutPlaintextResponse = GenerateDataKeyPairWithoutPlaintextResponse(nameonly PrivateKeyCiphertextBlob: Option<CiphertextType>, nameonly PublicKey: Option<PublicKeyType>, nameonly KeyId: Option<KeyIdType>, nameonly KeyPairSpec: Option<DataKeyPairSpec>)

  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(nameonly KeyId: KeyIdType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly NumberOfBytes: Option<NumberOfBytesType>, nameonly KeySpec: Option<DataKeySpec>, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyResponse = GenerateDataKeyResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly Plaintext: Option<PlaintextType>, nameonly KeyId: Option<KeyIdType>)

  datatype GenerateDataKeyWithoutPlaintextRequest = GenerateDataKeyWithoutPlaintextRequest(nameonly KeyId: KeyIdType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly KeySpec: Option<DataKeySpec>, nameonly NumberOfBytes: Option<NumberOfBytesType>, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyWithoutPlaintextResponse = GenerateDataKeyWithoutPlaintextResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly KeyId: Option<KeyIdType>)

  datatype GenerateRandomRequest = GenerateRandomRequest(nameonly NumberOfBytes: Option<NumberOfBytesType>, nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>)

  datatype GenerateRandomResponse = GenerateRandomResponse(nameonly Plaintext: Option<PlaintextType>)

  datatype GetKeyPolicyRequest = GetKeyPolicyRequest(nameonly KeyId: KeyIdType, nameonly PolicyName: PolicyNameType)

  datatype GetKeyPolicyResponse = GetKeyPolicyResponse(nameonly Policy: Option<PolicyType>)

  datatype GetKeyRotationStatusRequest = GetKeyRotationStatusRequest(nameonly KeyId: KeyIdType)

  datatype GetKeyRotationStatusResponse = GetKeyRotationStatusResponse(nameonly KeyRotationEnabled: Option<BooleanType>)

  datatype GetParametersForImportRequest = GetParametersForImportRequest(nameonly KeyId: KeyIdType, nameonly WrappingAlgorithm: AlgorithmSpec, nameonly WrappingKeySpec: WrappingKeySpec)

  datatype GetParametersForImportResponse = GetParametersForImportResponse(nameonly KeyId: Option<KeyIdType>, nameonly ImportToken: Option<CiphertextType>, nameonly PublicKey: Option<PlaintextType>, nameonly ParametersValidTo: Option<string>)

  datatype GetPublicKeyRequest = GetPublicKeyRequest(nameonly KeyId: KeyIdType, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GetPublicKeyResponse = GetPublicKeyResponse(nameonly KeyId: Option<KeyIdType>, nameonly PublicKey: Option<PublicKeyType>, nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec>, nameonly KeySpec: Option<KeySpec>, nameonly KeyUsage: Option<KeyUsageType>, nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList>, nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList>)

  datatype GrantConstraints = GrantConstraints(nameonly EncryptionContextSubset: Option<EncryptionContextType>, nameonly EncryptionContextEquals: Option<EncryptionContextType>)

  type GrantIdType = x: string
    | IsValid_GrantIdType(x)
    witness *

  type GrantList = seq<GrantListEntry>

  datatype GrantListEntry = GrantListEntry(nameonly KeyId: Option<KeyIdType>, nameonly GrantId: Option<GrantIdType>, nameonly Name: Option<GrantNameType>, nameonly CreationDate: Option<string>, nameonly GranteePrincipal: Option<PrincipalIdType>, nameonly RetiringPrincipal: Option<PrincipalIdType>, nameonly IssuingAccount: Option<PrincipalIdType>, nameonly Operations: Option<GrantOperationList>, nameonly Constraints: Option<GrantConstraints>)

  type GrantNameType = x: string
    | IsValid_GrantNameType(x)
    witness *

  datatype GrantOperation = Decrypt | Encrypt | GenerateDataKey | GenerateDataKeyWithoutPlaintext | ReEncryptFrom | ReEncryptTo | Sign | Verify | GetPublicKey | CreateGrant | RetireGrant | DescribeKey | GenerateDataKeyPair | GenerateDataKeyPairWithoutPlaintext

  type GrantOperationList = seq<GrantOperation>

  type GrantTokenList = x: seq<GrantTokenType>
    | IsValid_GrantTokenList(x)
    witness *

  type GrantTokenType = x: string
    | IsValid_GrantTokenType(x)
    witness *

  datatype ImportKeyMaterialRequest = ImportKeyMaterialRequest(nameonly KeyId: KeyIdType, nameonly ImportToken: CiphertextType, nameonly EncryptedKeyMaterial: CiphertextType, nameonly ValidTo: Option<string>, nameonly ExpirationModel: Option<ExpirationModelType>)

  datatype ImportKeyMaterialResponse = ImportKeyMaterialResponse

  type KeyIdType = x: string
    | IsValid_KeyIdType(x)
    witness *

  type KeyList = seq<KeyListEntry>

  datatype KeyListEntry = KeyListEntry(nameonly KeyId: Option<KeyIdType>, nameonly KeyArn: Option<ArnType>)

  trait {:termination false} IKeyManagementServiceClient {
    method CancelKeyDeletion(input: CancelKeyDeletionRequest) returns (output: Result<CancelKeyDeletionResponse, Error>)
      ensures CancelKeyDeletionCalledWith(input)
      ensures output.Success? ==> CancelKeyDeletionSucceededWith(input, output.value)
      decreases input

    method ConnectCustomKeyStore(input: ConnectCustomKeyStoreRequest) returns (output: Result<ConnectCustomKeyStoreResponse, Error>)
      ensures ConnectCustomKeyStoreCalledWith(input)
      ensures output.Success? ==> ConnectCustomKeyStoreSucceededWith(input, output.value)
      decreases input

    method CreateAlias(input: CreateAliasRequest) returns (output: Result<(), Error>)
      ensures CreateAliasCalledWith(input)
      ensures output.Success? ==> CreateAliasSucceededWith(input)
      decreases input

    method CreateCustomKeyStore(input: CreateCustomKeyStoreRequest) returns (output: Result<CreateCustomKeyStoreResponse, Error>)
      ensures CreateCustomKeyStoreCalledWith(input)
      ensures output.Success? ==> CreateCustomKeyStoreSucceededWith(input, output.value)
      decreases input

    method CreateGrant(input: CreateGrantRequest) returns (output: Result<CreateGrantResponse, Error>)
      ensures CreateGrantCalledWith(input)
      ensures output.Success? ==> CreateGrantSucceededWith(input, output.value)
      decreases input

    method CreateKey(input: CreateKeyRequest) returns (output: Result<CreateKeyResponse, Error>)
      ensures CreateKeyCalledWith(input)
      ensures output.Success? ==> CreateKeySucceededWith(input, output.value)
      decreases input

    method Decrypt(input: DecryptRequest) returns (output: Result<DecryptResponse, Error>)
      ensures DecryptCalledWith(input)
      ensures output.Success? ==> DecryptSucceededWith(input, output.value)
      decreases input

    method DeleteAlias(input: DeleteAliasRequest) returns (output: Result<(), Error>)
      ensures DeleteAliasCalledWith(input)
      ensures output.Success? ==> DeleteAliasSucceededWith(input)
      decreases input

    method DeleteCustomKeyStore(input: DeleteCustomKeyStoreRequest) returns (output: Result<DeleteCustomKeyStoreResponse, Error>)
      ensures DeleteCustomKeyStoreCalledWith(input)
      ensures output.Success? ==> DeleteCustomKeyStoreSucceededWith(input, output.value)
      decreases input

    method DeleteImportedKeyMaterial(input: DeleteImportedKeyMaterialRequest) returns (output: Result<(), Error>)
      ensures DeleteImportedKeyMaterialCalledWith(input)
      ensures output.Success? ==> DeleteImportedKeyMaterialSucceededWith(input)
      decreases input

    method DescribeCustomKeyStores(input: DescribeCustomKeyStoresRequest) returns (output: Result<DescribeCustomKeyStoresResponse, Error>)
      ensures DescribeCustomKeyStoresCalledWith(input)
      ensures output.Success? ==> DescribeCustomKeyStoresSucceededWith(input, output.value)
      decreases input

    method DescribeKey(input: DescribeKeyRequest) returns (output: Result<DescribeKeyResponse, Error>)
      ensures DescribeKeyCalledWith(input)
      ensures output.Success? ==> DescribeKeySucceededWith(input, output.value)
      decreases input

    method DisableKey(input: DisableKeyRequest) returns (output: Result<(), Error>)
      ensures DisableKeyCalledWith(input)
      ensures output.Success? ==> DisableKeySucceededWith(input)
      decreases input

    method DisableKeyRotation(input: DisableKeyRotationRequest) returns (output: Result<(), Error>)
      ensures DisableKeyRotationCalledWith(input)
      ensures output.Success? ==> DisableKeyRotationSucceededWith(input)
      decreases input

    method DisconnectCustomKeyStore(input: DisconnectCustomKeyStoreRequest) returns (output: Result<DisconnectCustomKeyStoreResponse, Error>)
      ensures DisconnectCustomKeyStoreCalledWith(input)
      ensures output.Success? ==> DisconnectCustomKeyStoreSucceededWith(input, output.value)
      decreases input

    method EnableKey(input: EnableKeyRequest) returns (output: Result<(), Error>)
      ensures EnableKeyCalledWith(input)
      ensures output.Success? ==> EnableKeySucceededWith(input)
      decreases input

    method EnableKeyRotation(input: EnableKeyRotationRequest) returns (output: Result<(), Error>)
      ensures EnableKeyRotationCalledWith(input)
      ensures output.Success? ==> EnableKeyRotationSucceededWith(input)
      decreases input

    method Encrypt(input: EncryptRequest) returns (output: Result<EncryptResponse, Error>)
      ensures EncryptCalledWith(input)
      ensures output.Success? ==> EncryptSucceededWith(input, output.value)
      decreases input

    method GenerateDataKey(input: GenerateDataKeyRequest) returns (output: Result<GenerateDataKeyResponse, Error>)
      ensures GenerateDataKeyCalledWith(input)
      ensures output.Success? ==> GenerateDataKeySucceededWith(input, output.value)
      decreases input

    method GenerateDataKeyPair(input: GenerateDataKeyPairRequest) returns (output: Result<GenerateDataKeyPairResponse, Error>)
      ensures GenerateDataKeyPairCalledWith(input)
      ensures output.Success? ==> GenerateDataKeyPairSucceededWith(input, output.value)
      decreases input

    method GenerateDataKeyPairWithoutPlaintext(input: GenerateDataKeyPairWithoutPlaintextRequest) returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
      ensures GenerateDataKeyPairWithoutPlaintextCalledWith(input)
      ensures output.Success? ==> GenerateDataKeyPairWithoutPlaintextSucceededWith(input, output.value)
      decreases input

    method GenerateDataKeyWithoutPlaintext(input: GenerateDataKeyWithoutPlaintextRequest) returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
      ensures GenerateDataKeyWithoutPlaintextCalledWith(input)
      ensures output.Success? ==> GenerateDataKeyWithoutPlaintextSucceededWith(input, output.value)
      decreases input

    method GenerateRandom(input: GenerateRandomRequest) returns (output: Result<GenerateRandomResponse, Error>)
      ensures GenerateRandomCalledWith(input)
      ensures output.Success? ==> GenerateRandomSucceededWith(input, output.value)
      decreases input

    method GetKeyPolicy(input: GetKeyPolicyRequest) returns (output: Result<GetKeyPolicyResponse, Error>)
      ensures GetKeyPolicyCalledWith(input)
      ensures output.Success? ==> GetKeyPolicySucceededWith(input, output.value)
      decreases input

    method GetKeyRotationStatus(input: GetKeyRotationStatusRequest) returns (output: Result<GetKeyRotationStatusResponse, Error>)
      ensures GetKeyRotationStatusCalledWith(input)
      ensures output.Success? ==> GetKeyRotationStatusSucceededWith(input, output.value)
      decreases input

    method GetParametersForImport(input: GetParametersForImportRequest) returns (output: Result<GetParametersForImportResponse, Error>)
      ensures GetParametersForImportCalledWith(input)
      ensures output.Success? ==> GetParametersForImportSucceededWith(input, output.value)
      decreases input

    method GetPublicKey(input: GetPublicKeyRequest) returns (output: Result<GetPublicKeyResponse, Error>)
      ensures GetPublicKeyCalledWith(input)
      ensures output.Success? ==> GetPublicKeySucceededWith(input, output.value)
      decreases input

    method ImportKeyMaterial(input: ImportKeyMaterialRequest) returns (output: Result<ImportKeyMaterialResponse, Error>)
      ensures ImportKeyMaterialCalledWith(input)
      ensures output.Success? ==> ImportKeyMaterialSucceededWith(input, output.value)
      decreases input

    method ListAliases(input: ListAliasesRequest) returns (output: Result<ListAliasesResponse, Error>)
      ensures ListAliasesCalledWith(input)
      ensures output.Success? ==> ListAliasesSucceededWith(input, output.value)
      decreases input

    method ListGrants(input: ListGrantsRequest) returns (output: Result<ListGrantsResponse, Error>)
      ensures ListGrantsCalledWith(input)
      ensures output.Success? ==> ListGrantsSucceededWith(input, output.value)
      decreases input

    method ListKeyPolicies(input: ListKeyPoliciesRequest) returns (output: Result<ListKeyPoliciesResponse, Error>)
      ensures ListKeyPoliciesCalledWith(input)
      ensures output.Success? ==> ListKeyPoliciesSucceededWith(input, output.value)
      decreases input

    method ListResourceTags(input: ListResourceTagsRequest) returns (output: Result<ListResourceTagsResponse, Error>)
      ensures ListResourceTagsCalledWith(input)
      ensures output.Success? ==> ListResourceTagsSucceededWith(input, output.value)
      decreases input

    method PutKeyPolicy(input: PutKeyPolicyRequest) returns (output: Result<(), Error>)
      ensures PutKeyPolicyCalledWith(input)
      ensures output.Success? ==> PutKeyPolicySucceededWith(input)
      decreases input

    method ReEncrypt(input: ReEncryptRequest) returns (output: Result<ReEncryptResponse, Error>)
      ensures ReEncryptCalledWith(input)
      ensures output.Success? ==> ReEncryptSucceededWith(input, output.value)
      decreases input

    method ReplicateKey(input: ReplicateKeyRequest) returns (output: Result<ReplicateKeyResponse, Error>)
      ensures ReplicateKeyCalledWith(input)
      ensures output.Success? ==> ReplicateKeySucceededWith(input, output.value)
      decreases input

    method RetireGrant(input: RetireGrantRequest) returns (output: Result<(), Error>)
      ensures RetireGrantCalledWith(input)
      ensures output.Success? ==> RetireGrantSucceededWith(input)
      decreases input

    method RevokeGrant(input: RevokeGrantRequest) returns (output: Result<(), Error>)
      ensures RevokeGrantCalledWith(input)
      ensures output.Success? ==> RevokeGrantSucceededWith(input)
      decreases input

    method ScheduleKeyDeletion(input: ScheduleKeyDeletionRequest) returns (output: Result<ScheduleKeyDeletionResponse, Error>)
      ensures ScheduleKeyDeletionCalledWith(input)
      ensures output.Success? ==> ScheduleKeyDeletionSucceededWith(input, output.value)
      decreases input

    method Sign(input: SignRequest) returns (output: Result<SignResponse, Error>)
      ensures SignCalledWith(input)
      ensures output.Success? ==> SignSucceededWith(input, output.value)
      decreases input

    method TagResource(input: TagResourceRequest) returns (output: Result<(), Error>)
      ensures TagResourceCalledWith(input)
      ensures output.Success? ==> TagResourceSucceededWith(input)
      decreases input

    method UntagResource(input: UntagResourceRequest) returns (output: Result<(), Error>)
      ensures UntagResourceCalledWith(input)
      ensures output.Success? ==> UntagResourceSucceededWith(input)
      decreases input

    method UpdateAlias(input: UpdateAliasRequest) returns (output: Result<(), Error>)
      ensures UpdateAliasCalledWith(input)
      ensures output.Success? ==> UpdateAliasSucceededWith(input)
      decreases input

    method UpdateCustomKeyStore(input: UpdateCustomKeyStoreRequest) returns (output: Result<UpdateCustomKeyStoreResponse, Error>)
      ensures UpdateCustomKeyStoreCalledWith(input)
      ensures output.Success? ==> UpdateCustomKeyStoreSucceededWith(input, output.value)
      decreases input

    method UpdateKeyDescription(input: UpdateKeyDescriptionRequest) returns (output: Result<(), Error>)
      ensures UpdateKeyDescriptionCalledWith(input)
      ensures output.Success? ==> UpdateKeyDescriptionSucceededWith(input)
      decreases input

    method UpdatePrimaryRegion(input: UpdatePrimaryRegionRequest) returns (output: Result<(), Error>)
      ensures UpdatePrimaryRegionCalledWith(input)
      ensures output.Success? ==> UpdatePrimaryRegionSucceededWith(input)
      decreases input

    method Verify(input: VerifyRequest) returns (output: Result<VerifyResponse, Error>)
      ensures VerifyCalledWith(input)
      ensures output.Success? ==> VerifySucceededWith(input, output.value)
      decreases input
  }

  datatype KeyManagerType = AWS | CUSTOMER

  datatype KeyMetadata = KeyMetadata(nameonly AWSAccountId: Option<AWSAccountIdType>, nameonly KeyId: KeyIdType, nameonly Arn: Option<ArnType>, nameonly CreationDate: Option<string>, nameonly Enabled: Option<BooleanType>, nameonly Description: Option<DescriptionType>, nameonly KeyUsage: Option<KeyUsageType>, nameonly KeyState: Option<KeyState>, nameonly DeletionDate: Option<string>, nameonly ValidTo: Option<string>, nameonly Origin: Option<OriginType>, nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType>, nameonly ExpirationModel: Option<ExpirationModelType>, nameonly KeyManager: Option<KeyManagerType>, nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec>, nameonly KeySpec: Option<KeySpec>, nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList>, nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList>, nameonly MultiRegion: Option<NullableBooleanType>, nameonly MultiRegionConfiguration: Option<MultiRegionConfiguration>, nameonly PendingDeletionWindowInDays: Option<PendingWindowInDaysType>)

  datatype KeySpec = RSA_2048 | RSA_3072 | RSA_4096 | ECC_NIST_P256 | ECC_NIST_P384 | ECC_NIST_P521 | ECC_SECG_P256K1 | SYMMETRIC_DEFAULT

  datatype KeyState = Creating | Enabled | Disabled | PendingDeletion | PendingImport | PendingReplicaDeletion | Unavailable | Updating

  type KeyStorePasswordType = x: string
    | IsValid_KeyStorePasswordType(x)
    witness *

  datatype KeyUsageType = SIGN_VERIFY | ENCRYPT_DECRYPT

  type LimitType = x: int32
    | IsValid_LimitType(x)
    witness *

  datatype ListAliasesRequest = ListAliasesRequest(nameonly KeyId: Option<KeyIdType>, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListAliasesResponse = ListAliasesResponse(nameonly Aliases: Option<AliasList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListGrantsRequest = ListGrantsRequest(nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>, nameonly KeyId: KeyIdType, nameonly GrantId: Option<GrantIdType>, nameonly GranteePrincipal: Option<PrincipalIdType>)

  datatype ListGrantsResponse = ListGrantsResponse(nameonly Grants: Option<GrantList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListKeyPoliciesRequest = ListKeyPoliciesRequest(nameonly KeyId: KeyIdType, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListKeyPoliciesResponse = ListKeyPoliciesResponse(nameonly PolicyNames: Option<PolicyNameList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListKeysRequest = ListKeysRequest(nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListResourceTagsRequest = ListResourceTagsRequest(nameonly KeyId: KeyIdType, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListResourceTagsResponse = ListResourceTagsResponse(nameonly Tags: Option<TagList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListRetirableGrantsRequest = ListRetirableGrantsRequest(nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>, nameonly RetiringPrincipal: PrincipalIdType)

  type MarkerType = x: string
    | IsValid_MarkerType(x)
    witness *

  datatype MessageType = RAW | DIGEST

  datatype MultiRegionConfiguration = MultiRegionConfiguration(nameonly MultiRegionKeyType: Option<MultiRegionKeyType>, nameonly PrimaryKey: Option<MultiRegionKey>, nameonly ReplicaKeys: Option<MultiRegionKeyList>)

  datatype MultiRegionKey = MultiRegionKey(nameonly Arn: Option<ArnType>, nameonly Region: Option<RegionType>)

  type MultiRegionKeyList = seq<MultiRegionKey>

  datatype MultiRegionKeyType = PRIMARY | REPLICA

  type NullableBooleanType = bool

  type NumberOfBytesType = x: int32
    | IsValid_NumberOfBytesType(x)
    witness *

  datatype OriginType = AWS_KMS | EXTERNAL | AWS_CLOUDHSM

  type PendingWindowInDaysType = x: int32
    | IsValid_PendingWindowInDaysType(x)
    witness *

  type PlaintextType = x: seq<uint8>
    | IsValid_PlaintextType(x)
    witness *

  type PolicyNameList = seq<PolicyNameType>

  type PolicyNameType = x: string
    | IsValid_PolicyNameType(x)
    witness *

  type PolicyType = x: string
    | IsValid_PolicyType(x)
    witness *

  type PrincipalIdType = x: string
    | IsValid_PrincipalIdType(x)
    witness *

  type PublicKeyType = x: seq<uint8>
    | IsValid_PublicKeyType(x)
    witness *

  datatype PutKeyPolicyRequest = PutKeyPolicyRequest(nameonly KeyId: KeyIdType, nameonly PolicyName: PolicyNameType, nameonly Policy: PolicyType, nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType>)

  datatype ReEncryptRequest = ReEncryptRequest(nameonly CiphertextBlob: CiphertextType, nameonly SourceEncryptionContext: Option<EncryptionContextType>, nameonly SourceKeyId: Option<KeyIdType>, nameonly DestinationKeyId: KeyIdType, nameonly DestinationEncryptionContext: Option<EncryptionContextType>, nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>, nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>, nameonly GrantTokens: Option<GrantTokenList>)

  datatype ReEncryptResponse = ReEncryptResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly SourceKeyId: Option<KeyIdType>, nameonly KeyId: Option<KeyIdType>, nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>, nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  type RegionType = x: string
    | IsValid_RegionType(x)
    witness *

  datatype ReplicateKeyRequest = ReplicateKeyRequest(nameonly KeyId: KeyIdType, nameonly ReplicaRegion: RegionType, nameonly Policy: Option<PolicyType>, nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType>, nameonly Description: Option<DescriptionType>, nameonly Tags: Option<TagList>)

  datatype ReplicateKeyResponse = ReplicateKeyResponse(nameonly ReplicaKeyMetadata: Option<KeyMetadata>, nameonly ReplicaPolicy: Option<PolicyType>, nameonly ReplicaTags: Option<TagList>)

  datatype RetireGrantRequest = RetireGrantRequest(nameonly GrantToken: Option<GrantTokenType>, nameonly KeyId: Option<KeyIdType>, nameonly GrantId: Option<GrantIdType>)

  datatype RevokeGrantRequest = RevokeGrantRequest(nameonly KeyId: KeyIdType, nameonly GrantId: GrantIdType)

  datatype ScheduleKeyDeletionRequest = ScheduleKeyDeletionRequest(nameonly KeyId: KeyIdType, nameonly PendingWindowInDays: Option<PendingWindowInDaysType>)

  datatype ScheduleKeyDeletionResponse = ScheduleKeyDeletionResponse(nameonly KeyId: Option<KeyIdType>, nameonly DeletionDate: Option<string>, nameonly KeyState: Option<KeyState>, nameonly PendingWindowInDays: Option<PendingWindowInDaysType>)

  datatype SigningAlgorithmSpec = RSASSA_PSS_SHA_256 | RSASSA_PSS_SHA_384 | RSASSA_PSS_SHA_512 | RSASSA_PKCS1_V1_5_SHA_256 | RSASSA_PKCS1_V1_5_SHA_384 | RSASSA_PKCS1_V1_5_SHA_512 | ECDSA_SHA_256 | ECDSA_SHA_384 | ECDSA_SHA_512

  type SigningAlgorithmSpecList = seq<SigningAlgorithmSpec>

  datatype SignRequest = SignRequest(nameonly KeyId: KeyIdType, nameonly Message: PlaintextType, nameonly MessageType: Option<MessageType>, nameonly GrantTokens: Option<GrantTokenList>, nameonly SigningAlgorithm: SigningAlgorithmSpec)

  datatype SignResponse = SignResponse(nameonly KeyId: Option<KeyIdType>, nameonly Signature: Option<CiphertextType>, nameonly SigningAlgorithm: Option<SigningAlgorithmSpec>)

  datatype Tag = Tag(nameonly TagKey: TagKeyType, nameonly TagValue: TagValueType)

  type TagKeyList = seq<TagKeyType>

  type TagKeyType = x: string
    | IsValid_TagKeyType(x)
    witness *

  type TagList = seq<Tag>

  datatype TagResourceRequest = TagResourceRequest(nameonly KeyId: KeyIdType, nameonly Tags: TagList)

  type TagValueType = x: string
    | IsValid_TagValueType(x)
    witness *

  type TrustAnchorCertificateType = x: string
    | IsValid_TrustAnchorCertificateType(x)
    witness *

  datatype UntagResourceRequest = UntagResourceRequest(nameonly KeyId: KeyIdType, nameonly TagKeys: TagKeyList)

  datatype UpdateAliasRequest = UpdateAliasRequest(nameonly AliasName: AliasNameType, nameonly TargetKeyId: KeyIdType)

  datatype UpdateCustomKeyStoreRequest = UpdateCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType, nameonly NewCustomKeyStoreName: Option<CustomKeyStoreNameType>, nameonly KeyStorePassword: Option<KeyStorePasswordType>, nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType>)

  datatype UpdateCustomKeyStoreResponse = UpdateCustomKeyStoreResponse

  datatype UpdateKeyDescriptionRequest = UpdateKeyDescriptionRequest(nameonly KeyId: KeyIdType, nameonly Description: DescriptionType)

  datatype UpdatePrimaryRegionRequest = UpdatePrimaryRegionRequest(nameonly KeyId: KeyIdType, nameonly PrimaryRegion: RegionType)

  datatype VerifyRequest = VerifyRequest(nameonly KeyId: KeyIdType, nameonly Message: PlaintextType, nameonly MessageType: Option<MessageType>, nameonly Signature: CiphertextType, nameonly SigningAlgorithm: SigningAlgorithmSpec, nameonly GrantTokens: Option<GrantTokenList>)

  datatype VerifyResponse = VerifyResponse(nameonly KeyId: Option<KeyIdType>, nameonly SignatureValid: Option<BooleanType>, nameonly SigningAlgorithm: Option<SigningAlgorithmSpec>)

  datatype WrappingKeySpec = RSA_2048

  datatype Error = CloudHsmClusterNotFoundException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreHasCMKsException(nameonly message: Option<ErrorMessageType>) | TagException(nameonly message: Option<ErrorMessageType>) | InvalidImportTokenException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterNotRelatedException(nameonly message: Option<ErrorMessageType>) | DependencyTimeoutException(nameonly message: Option<ErrorMessageType>) | InvalidGrantIdException(nameonly message: Option<ErrorMessageType>) | MalformedPolicyDocumentException(nameonly message: Option<ErrorMessageType>) | ExpiredImportTokenException(nameonly message: Option<ErrorMessageType>) | UnsupportedOperationException(nameonly message: Option<ErrorMessageType>) | InvalidGrantTokenException(nameonly message: Option<ErrorMessageType>) | KeyUnavailableException(nameonly message: Option<ErrorMessageType>) | KMSInternalException(nameonly message: Option<ErrorMessageType>) | IncorrectKeyMaterialException(nameonly message: Option<ErrorMessageType>) | InvalidCiphertextException(nameonly message: Option<ErrorMessageType>) | IncorrectTrustAnchorException(nameonly message: Option<ErrorMessageType>) | InvalidMarkerException(nameonly message: Option<ErrorMessageType>) | LimitExceededException(nameonly message: Option<ErrorMessageType>) | InvalidKeyUsageException(nameonly message: Option<ErrorMessageType>) | AlreadyExistsException(nameonly message: Option<ErrorMessageType>) | InvalidArnException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreNotFoundException(nameonly message: Option<ErrorMessageType>) | InvalidAliasNameException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterInUseException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterInvalidConfigurationException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreNameInUseException(nameonly message: Option<ErrorMessageType>) | KMSInvalidSignatureException(nameonly message: Option<ErrorMessageType>) | KMSInvalidStateException(nameonly message: Option<ErrorMessageType>) | IncorrectKeyException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterNotActiveException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreInvalidStateException(nameonly message: Option<ErrorMessageType>) | DisabledException(nameonly message: Option<ErrorMessageType>) | NotFoundException(nameonly message: Option<ErrorMessageType>) | Opaque(obj: object)

  type OpaqueError = e: Error
    | e.Opaque?
    witness *

  predicate method IsValid_AliasNameType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_ArnType(x: string)
    decreases x
  {
    20 <= |x| <= 2048
  }

  predicate method IsValid_CiphertextType(x: seq<uint8>)
    decreases x
  {
    1 <= |x| <= 6144
  }

  predicate method IsValid_CloudHsmClusterIdType(x: string)
    decreases x
  {
    19 <= |x| <= 24
  }

  predicate method IsValid_CustomKeyStoreIdType(x: string)
    decreases x
  {
    1 <= |x| <= 64
  }

  predicate method IsValid_CustomKeyStoreNameType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_DescriptionType(x: string)
    decreases x
  {
    0 <= |x| <= 8192
  }

  predicate method IsValid_GrantIdType(x: string)
    decreases x
  {
    1 <= |x| <= 128
  }

  predicate method IsValid_GrantNameType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_GrantTokenList(x: seq<GrantTokenType>)
    decreases x
  {
    0 <= |x| <= 10
  }

  predicate method IsValid_GrantTokenType(x: string)
    decreases x
  {
    1 <= |x| <= 8192
  }

  predicate method IsValid_KeyIdType(x: string)
    decreases x
  {
    1 <= |x| <= 2048
  }

  predicate {:opaque} {:fuel 0, 0} CancelKeyDeletionCalledWith(input: CancelKeyDeletionRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CancelKeyDeletionSucceededWith(input: CancelKeyDeletionRequest, output: CancelKeyDeletionResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ConnectCustomKeyStoreCalledWith(input: ConnectCustomKeyStoreRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ConnectCustomKeyStoreSucceededWith(input: ConnectCustomKeyStoreRequest, output: ConnectCustomKeyStoreResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateAliasCalledWith(input: CreateAliasRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateAliasSucceededWith(input: CreateAliasRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateCustomKeyStoreCalledWith(input: CreateCustomKeyStoreRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateCustomKeyStoreSucceededWith(input: CreateCustomKeyStoreRequest, output: CreateCustomKeyStoreResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateGrantCalledWith(input: CreateGrantRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateGrantSucceededWith(input: CreateGrantRequest, output: CreateGrantResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateKeyCalledWith(input: CreateKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} CreateKeySucceededWith(input: CreateKeyRequest, output: CreateKeyResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DecryptCalledWith(input: DecryptRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DecryptSucceededWith(input: DecryptRequest, output: DecryptResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DeleteAliasCalledWith(input: DeleteAliasRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DeleteAliasSucceededWith(input: DeleteAliasRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DeleteCustomKeyStoreCalledWith(input: DeleteCustomKeyStoreRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DeleteCustomKeyStoreSucceededWith(input: DeleteCustomKeyStoreRequest, output: DeleteCustomKeyStoreResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DeleteImportedKeyMaterialCalledWith(input: DeleteImportedKeyMaterialRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DeleteImportedKeyMaterialSucceededWith(input: DeleteImportedKeyMaterialRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DescribeCustomKeyStoresCalledWith(input: DescribeCustomKeyStoresRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DescribeCustomKeyStoresSucceededWith(input: DescribeCustomKeyStoresRequest, output: DescribeCustomKeyStoresResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DescribeKeyCalledWith(input: DescribeKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DescribeKeySucceededWith(input: DescribeKeyRequest, output: DescribeKeyResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DisableKeyCalledWith(input: DisableKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DisableKeySucceededWith(input: DisableKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DisableKeyRotationCalledWith(input: DisableKeyRotationRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DisableKeyRotationSucceededWith(input: DisableKeyRotationRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DisconnectCustomKeyStoreCalledWith(input: DisconnectCustomKeyStoreRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DisconnectCustomKeyStoreSucceededWith(input: DisconnectCustomKeyStoreRequest, output: DisconnectCustomKeyStoreResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EnableKeyCalledWith(input: EnableKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EnableKeySucceededWith(input: EnableKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EnableKeyRotationCalledWith(input: EnableKeyRotationRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EnableKeyRotationSucceededWith(input: EnableKeyRotationRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EncryptCalledWith(input: EncryptRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EncryptSucceededWith(input: EncryptRequest, output: EncryptResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyCalledWith(input: GenerateDataKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeySucceededWith(input: GenerateDataKeyRequest, output: GenerateDataKeyResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyPairCalledWith(input: GenerateDataKeyPairRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyPairSucceededWith(input: GenerateDataKeyPairRequest, output: GenerateDataKeyPairResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyPairWithoutPlaintextCalledWith(input: GenerateDataKeyPairWithoutPlaintextRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyPairWithoutPlaintextSucceededWith(input: GenerateDataKeyPairWithoutPlaintextRequest, output: GenerateDataKeyPairWithoutPlaintextResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyWithoutPlaintextCalledWith(input: GenerateDataKeyWithoutPlaintextRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyWithoutPlaintextSucceededWith(input: GenerateDataKeyWithoutPlaintextRequest, output: GenerateDataKeyWithoutPlaintextResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateRandomCalledWith(input: GenerateRandomRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateRandomSucceededWith(input: GenerateRandomRequest, output: GenerateRandomResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetKeyPolicyCalledWith(input: GetKeyPolicyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetKeyPolicySucceededWith(input: GetKeyPolicyRequest, output: GetKeyPolicyResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetKeyRotationStatusCalledWith(input: GetKeyRotationStatusRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetKeyRotationStatusSucceededWith(input: GetKeyRotationStatusRequest, output: GetKeyRotationStatusResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetParametersForImportCalledWith(input: GetParametersForImportRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetParametersForImportSucceededWith(input: GetParametersForImportRequest, output: GetParametersForImportResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetPublicKeyCalledWith(input: GetPublicKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GetPublicKeySucceededWith(input: GetPublicKeyRequest, output: GetPublicKeyResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ImportKeyMaterialCalledWith(input: ImportKeyMaterialRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ImportKeyMaterialSucceededWith(input: ImportKeyMaterialRequest, output: ImportKeyMaterialResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListAliasesCalledWith(input: ListAliasesRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListAliasesSucceededWith(input: ListAliasesRequest, output: ListAliasesResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListGrantsCalledWith(input: ListGrantsRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListGrantsSucceededWith(input: ListGrantsRequest, output: ListGrantsResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListKeyPoliciesCalledWith(input: ListKeyPoliciesRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListKeyPoliciesSucceededWith(input: ListKeyPoliciesRequest, output: ListKeyPoliciesResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListResourceTagsCalledWith(input: ListResourceTagsRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ListResourceTagsSucceededWith(input: ListResourceTagsRequest, output: ListResourceTagsResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} PutKeyPolicyCalledWith(input: PutKeyPolicyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} PutKeyPolicySucceededWith(input: PutKeyPolicyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ReEncryptCalledWith(input: ReEncryptRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ReEncryptSucceededWith(input: ReEncryptRequest, output: ReEncryptResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ReplicateKeyCalledWith(input: ReplicateKeyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ReplicateKeySucceededWith(input: ReplicateKeyRequest, output: ReplicateKeyResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} RetireGrantCalledWith(input: RetireGrantRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} RetireGrantSucceededWith(input: RetireGrantRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} RevokeGrantCalledWith(input: RevokeGrantRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} RevokeGrantSucceededWith(input: RevokeGrantRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ScheduleKeyDeletionCalledWith(input: ScheduleKeyDeletionRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} ScheduleKeyDeletionSucceededWith(input: ScheduleKeyDeletionRequest, output: ScheduleKeyDeletionResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} SignCalledWith(input: SignRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} SignSucceededWith(input: SignRequest, output: SignResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} TagResourceCalledWith(input: TagResourceRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} TagResourceSucceededWith(input: TagResourceRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UntagResourceCalledWith(input: UntagResourceRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UntagResourceSucceededWith(input: UntagResourceRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdateAliasCalledWith(input: UpdateAliasRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdateAliasSucceededWith(input: UpdateAliasRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdateCustomKeyStoreCalledWith(input: UpdateCustomKeyStoreRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdateCustomKeyStoreSucceededWith(input: UpdateCustomKeyStoreRequest, output: UpdateCustomKeyStoreResponse)
    decreases input, output
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdateKeyDescriptionCalledWith(input: UpdateKeyDescriptionRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdateKeyDescriptionSucceededWith(input: UpdateKeyDescriptionRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdatePrimaryRegionCalledWith(input: UpdatePrimaryRegionRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} UpdatePrimaryRegionSucceededWith(input: UpdatePrimaryRegionRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} VerifyCalledWith(input: VerifyRequest)
    decreases input
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} VerifySucceededWith(input: VerifyRequest, output: VerifyResponse)
    decreases input, output
  {
    true
  }

  predicate method IsValid_KeyStorePasswordType(x: string)
    decreases x
  {
    7 <= |x| <= 32
  }

  predicate method IsValid_LimitType(x: int32)
    decreases x
  {
    1 <= x <= 1000
  }

  predicate method IsValid_MarkerType(x: string)
    decreases x
  {
    1 <= |x| <= 1024
  }

  predicate method IsValid_NumberOfBytesType(x: int32)
    decreases x
  {
    1 <= x <= 1024
  }

  predicate method IsValid_PendingWindowInDaysType(x: int32)
    decreases x
  {
    1 <= x <= 365
  }

  predicate method IsValid_PlaintextType(x: seq<uint8>)
    decreases x
  {
    1 <= |x| <= 4096
  }

  predicate method IsValid_PolicyNameType(x: string)
    decreases x
  {
    1 <= |x| <= 128
  }

  predicate method IsValid_PolicyType(x: string)
    decreases x
  {
    1 <= |x| <= 131072
  }

  predicate method IsValid_PrincipalIdType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_PublicKeyType(x: seq<uint8>)
    decreases x
  {
    1 <= |x| <= 8192
  }

  predicate method IsValid_RegionType(x: string)
    decreases x
  {
    1 <= |x| <= 32
  }

  predicate method IsValid_TagKeyType(x: string)
    decreases x
  {
    1 <= |x| <= 128
  }

  predicate method IsValid_TagValueType(x: string)
    decreases x
  {
    0 <= |x| <= 256
  }

  predicate method IsValid_TrustAnchorCertificateType(x: string)
    decreases x
  {
    1 <= |x| <= 5000
  }
}

abstract module ComAmazonawsKmsAbstract {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = ComAmazonawsKmsTypes
  datatype KMSClientConfigType = KMSClientConfigType

  function method DefaultKMSClientConfigType(): KMSClientConfigType

  method {:extern} KMSClient(config: KMSClientConfigType := DefaultKMSClientConfigType()) returns (res: Result<IKeyManagementServiceClient, Error>)
    decreases config
}

module StandardLibrary {

  import opened Wrappers

  import opened U = UInt
  lemma SeqTakeAppend<A>(s: seq<A>, i: int)
    requires 0 <= i < |s|
    ensures s[..i] + [s[i]] == s[..i + 1]
    decreases s, i
  {
  }

  function method {:tailrecursion} Join<T>(ss: seq<seq<T>>, joiner: seq<T>): (s: seq<T>)
    requires 0 < |ss|
    decreases ss, joiner
  {
    if |ss| == 1 then
      ss[0]
    else
      ss[0] + joiner + Join(ss[1..], joiner)
  }

  function method {:tailrecursion} Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i: int :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i: Option<nat> := FindIndexMatching(s, delim, 0);
    if i.Some? then
      [s[..i.value]] + Split(s[i.value + 1..], delim)
    else
      [s]
  }

  lemma /*{:_induction s}*/ WillSplitOnDelim<T>(s: seq<T>, delim: T, prefix: seq<T>)
    requires |prefix| < |s|
    requires forall i: int :: 0 <= i < |prefix| ==> prefix[i] == s[i]
    requires delim !in prefix && s[|prefix|] == delim
    ensures Split(s, delim) == [prefix] + Split(s[|prefix| + 1..], delim)
    decreases s, prefix
  {
  }

  lemma /*{:_induction s}*/ WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
    decreases s
  {
  }

  lemma FindIndexMatchingLocatesElem<T>(s: seq<T>, c: T, start: nat, elemIndex: nat)
    requires start <= elemIndex <= |s|
    requires forall i: int :: start <= i < elemIndex ==> s[i] != c
    requires elemIndex == |s| || s[elemIndex] == c
    ensures FindIndexMatching(s, c, start) == if elemIndex == |s| then None else Some(elemIndex)
    decreases elemIndex - start
  {
  }

  function method FindIndexMatching<T(==)>(s: seq<T>, c: T, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && s[index.value] == c && c !in s[i .. index.value]
    ensures index.None? ==> c !in s[i..]
    decreases |s| - i
  {
    FindIndex(s, (x: T) => x == c, i)
  }

  function method {:tailrecursion} FindIndex<T>(s: seq<T>, f: T -> bool, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && f(s[index.value]) && forall j: int :: i <= j < index.value ==> !f(s[j])
    ensures index.None? ==> forall j: int :: i <= j < |s| ==> !f(s[j])
    decreases |s| - i
  {
    if i == |s| then
      None
    else if f(s[i]) then
      Some(i)
    else
      FindIndex(s, f, i + 1)
  }

  function method {:tailrecursion} Filter<T>(s: seq<T>, f: T -> bool): (res: seq<T>)
    ensures forall i: int :: 0 <= i < |s| && f(s[i]) ==> s[i] in res
    ensures forall i: int :: 0 <= i < |res| ==> res[i] in s && f(res[i])
    ensures |res| <= |s|
    decreases s
  {
    if |s| == 0 then
      []
    else if f(s[0]) then
      [s[0]] + Filter(s[1..], f)
    else
      Filter(s[1..], f)
  }

  lemma /*{:_induction s, s', f}*/ FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s + s', f) == Filter(s, f) + Filter(s', f)
    decreases s, s'
  {
  }

  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i: int :: 0 <= i < n ==> Fill(value, n)[i] == value
    decreases n
  {
    seq(n, (_: int) => value)
  }

  method SeqToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires 0 <= i <= |s|
    ensures s[..i] + s[i..] == s
    decreases s, i
  {
  }

  predicate method LexicographicLessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    decreases a, b
  {
    exists k: int :: 
      0 <= k <= |a| &&
      LexicographicLessOrEqualAux(a, b, less, k)
  }

  predicate method LexicographicLessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
    decreases a, b, lengthOfCommonPrefix
  {
    lengthOfCommonPrefix <= |b| &&
    (forall i: int :: 
      0 <= i < lengthOfCommonPrefix ==>
        a[i] == b[i]) &&
    (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

  predicate Trichotomous<T(!new)>(less: (T, T) -> bool)
  {
    (forall x: T, y: T :: 
      less(x, y) || x == y || less(y, x)) &&
    (forall x: T, y: T :: 
      less(x, y) &&
      less(y, x) ==>
        false) &&
    forall x: T, y: T :: 
      less(x, y) ==>
        x != y
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T, z: T :: 
      R(x, y) &&
      R(y, z) ==>
        R(x, z)
  }

  lemma UInt8LessIsTrichotomousTransitive()
    ensures Trichotomous(UInt8Less)
    ensures Transitive(UInt8Less)
  {
  }

  lemma LexIsReflexive<T>(a: seq<T>, less: (T, T) -> bool)
    ensures LexicographicLessOrEqual(a, a, less)
    decreases a
  {
  }

  lemma LexIsAntisymmetric<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, a, less)
    ensures a == b
    decreases a, b
  {
  }

  lemma LexIsTransitive<T>(a: seq<T>, b: seq<T>, c: seq<T>, less: (T, T) -> bool)
    requires Transitive(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, c, less)
    ensures LexicographicLessOrEqual(a, c, less)
    decreases a, b, c
  {
  }

  lemma LexIsTotal<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    ensures LexicographicLessOrEqual(a, b, less) || LexicographicLessOrEqual(b, a, less)
    decreases a, b
  {
  }

  function method {:tailrecursion} SetToOrderedSequence<T(==,!new)>(s: set<seq<T>>, less: (T, T) -> bool): (q: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures |s| == |q|
    ensures forall i: int :: 0 <= i < |q| ==> q[i] in s
    ensures forall k: seq<T> :: k in s ==> k in q
    ensures forall i: int :: 0 < i < |q| ==> LexicographicLessOrEqual(q[i - 1], q[i], less)
    ensures forall i: int, j: int | 0 <= i < j < |q| :: q[i] != q[j]
    decreases s
  {
    if s == {} then
      []
    else
      ThereIsAMinimum(s, less); assert forall a: seq<T>, b: seq<T> :: IsMinimum(a, s, less) && IsMinimum(b, s, less) ==> a == b by {
    forall a: seq<T>, b: seq<T> | IsMinimum(a, s, less) && IsMinimum(b, s, less) {
      MinimumIsUnique(a, b, s, less);
    }
  } var a: seq<T> :| a in s && IsMinimum(a, s, less); [a] + SetToOrderedSequence(s - {a}, less)
  }

  predicate method IsMinimum<T(==)>(a: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    decreases a, s
  {
    a in s &&
    forall z: seq<T> :: 
      z in s ==>
        LexicographicLessOrEqual(a, z, less)
  }

  lemma ThereIsAMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures exists a: seq<T> :: IsMinimum(a, s, less)
    decreases s
  {
  }

  lemma MinimumIsUnique<T>(a: seq<T>, b: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    requires IsMinimum(a, s, less) && IsMinimum(b, s, less)
    requires Trichotomous(less)
    ensures a == b
    decreases a, b, s
  {
  }

  lemma FindMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool) returns (a: seq<T>)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures IsMinimum(a, s, less)
    decreases s
  {
  }

  module UInt {
    newtype uint8 = x: int
      | 0 <= x < 256

    newtype uint16 = x: int
      | 0 <= x < 65536

    newtype uint32 = x: int
      | 0 <= x < 4294967296

    newtype uint64 = x: int
      | 0 <= x < 18446744073709551616

    newtype int32 = x: int
      | -2147483648 <= x < 2147483648

    newtype int64 = x: int
      | -9223372036854775808 <= x < 9223372036854775808

    newtype posInt64 = x: int
      | 0 < x < 9223372036854775808
      witness 1

    type seq16<T> = s: seq<T>
      | HasUint16Len(s)

    type Uint8Seq16 = seq16<uint8>

    type seq32<T> = s: seq<T>
      | HasUint32Len(s)

    type Uint8Seq32 = seq32<uint8>

    type seq64<T> = s: seq<T>
      | HasUint64Len(s)

    type Uint8Seq64 = seq64<uint8>

    const UINT16_LIMIT := 65536
    const UINT32_LIMIT := 4294967296
    const UINT64_LIMIT := 18446744073709551616
    const INT32_MAX_LIMIT := 2147483648
    const INT64_MAX_LIMIT := 9223372036854775808

    predicate method UInt8Less(a: uint8, b: uint8)
      decreases a, b
    {
      a < b
    }

    predicate method HasUint16Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT16_LIMIT
    }

    predicate method HasUint32Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT32_LIMIT
    }

    predicate method HasUint64Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT64_LIMIT
    }

    function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
      ensures |ret| == 2
      ensures 256 * ret[0] as uint16 + ret[1] as uint16 == x
      decreases x
    {
      var b0: uint8 := (x / 256) as uint8;
      var b1: uint8 := (x % 256) as uint8;
      [b0, b1]
    }

    function method SeqToUInt16(s: seq<uint8>): (x: uint16)
      requires |s| == 2
      ensures UInt16ToSeq(x) == s
      ensures x >= 0
      decreases s
    {
      var x0: uint16 := s[0] as uint16 * 256;
      x0 + s[1] as uint16
    }

    lemma UInt16SeqSerializeDeserialize(x: uint16)
      ensures SeqToUInt16(UInt16ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt16SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 2
      ensures UInt16ToSeq(SeqToUInt16(s)) == s
      decreases s
    {
    }

    function method UInt32ToSeq(x: uint32): (ret: seq<uint8>)
      ensures |ret| == 4
      ensures 16777216 * ret[0] as uint32 + 65536 * ret[1] as uint32 + 256 * ret[2] as uint32 + ret[3] as uint32 == x
      decreases x
    {
      var b0: uint8 := (x / 16777216) as uint8;
      var x0: uint32 := x - b0 as uint32 * 16777216;
      var b1: uint8 := (x0 / 65536) as uint8;
      var x1: uint32 := x0 - b1 as uint32 * 65536;
      var b2: uint8 := (x1 / 256) as uint8;
      var b3: uint8 := (x1 % 256) as uint8;
      [b0, b1, b2, b3]
    }

    function method SeqToUInt32(s: seq<uint8>): (x: uint32)
      requires |s| == 4
      ensures UInt32ToSeq(x) == s
      decreases s
    {
      var x0: uint32 := s[0] as uint32 * 16777216;
      var x1: uint32 := x0 + s[1] as uint32 * 65536;
      var x2: uint32 := x1 + s[2] as uint32 * 256;
      x2 + s[3] as uint32
    }

    lemma UInt32SeqSerializeDeserialize(x: uint32)
      ensures SeqToUInt32(UInt32ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt32SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 4
      ensures UInt32ToSeq(SeqToUInt32(s)) == s
      decreases s
    {
    }

    function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
      ensures |ret| == 8
      ensures 72057594037927936 * ret[0] as uint64 + 281474976710656 * ret[1] as uint64 + 1099511627776 * ret[2] as uint64 + 4294967296 * ret[3] as uint64 + 16777216 * ret[4] as uint64 + 65536 * ret[5] as uint64 + 256 * ret[6] as uint64 + ret[7] as uint64 == x
      decreases x
    {
      var b0: uint8 := (x / 72057594037927936) as uint8;
      var x0: uint64 := x - b0 as uint64 * 72057594037927936;
      var b1: uint8 := (x0 / 281474976710656) as uint8;
      var x1: uint64 := x0 - b1 as uint64 * 281474976710656;
      var b2: uint8 := (x1 / 1099511627776) as uint8;
      var x2: uint64 := x1 - b2 as uint64 * 1099511627776;
      var b3: uint8 := (x2 / 4294967296) as uint8;
      var x3: uint64 := x2 - b3 as uint64 * 4294967296;
      var b4: uint8 := (x3 / 16777216) as uint8;
      var x4: uint64 := x3 - b4 as uint64 * 16777216;
      var b5: uint8 := (x4 / 65536) as uint8;
      var x5: uint64 := x4 - b5 as uint64 * 65536;
      var b6: uint8 := (x5 / 256) as uint8;
      var b7: uint8 := (x5 % 256) as uint8;
      [b0, b1, b2, b3, b4, b5, b6, b7]
    }

    function method SeqToUInt64(s: seq<uint8>): (x: uint64)
      requires |s| == 8
      ensures UInt64ToSeq(x) == s
      decreases s
    {
      var x0: uint64 := s[0] as uint64 * 72057594037927936;
      var x1: uint64 := x0 + s[1] as uint64 * 281474976710656;
      var x2: uint64 := x1 + s[2] as uint64 * 1099511627776;
      var x3: uint64 := x2 + s[3] as uint64 * 4294967296;
      var x4: uint64 := x3 + s[4] as uint64 * 16777216;
      var x5: uint64 := x4 + s[5] as uint64 * 65536;
      var x6: uint64 := x5 + s[6] as uint64 * 256;
      var x: uint64 := x6 + s[7] as uint64;
      UInt64SeqSerialize(x, s);
      x
    }

    lemma UInt64SeqSerialize(x: uint64, s: seq<uint8>)
      requires |s| == 8
      requires 72057594037927936 * s[0] as uint64 + 281474976710656 * s[1] as uint64 + 1099511627776 * s[2] as uint64 + 4294967296 * s[3] as uint64 + 16777216 * s[4] as uint64 + 65536 * s[5] as uint64 + 256 * s[6] as uint64 + s[7] as uint64 == x
      ensures UInt64ToSeq(x) == s
      decreases x, s
    {
    }

    lemma UInt64SeqSerializeDeserialize(x: uint64)
      ensures SeqToUInt64(UInt64ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt64SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 8
      ensures UInt64ToSeq(SeqToUInt64(s)) == s
      decreases s
    {
    }

    function SeqToNat(s: seq<uint8>): nat
      decreases s
    {
      if s == [] then
        0
      else
        ghost var finalIndex: int := |s| - 1; SeqToNat(s[..finalIndex]) * 256 + s[finalIndex] as nat
    }

    lemma /*{:_induction s}*/ SeqToNatZeroPrefix(s: seq<uint8>)
      ensures SeqToNat(s) == SeqToNat([0] + s)
      decreases s
    {
    }

    lemma /*{:_induction s}*/ SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
      requires n < UINT32_LIMIT
      requires 4 <= |s|
      requires ghost var suffixStartIndex: int := |s| - 4; s[suffixStartIndex..] == UInt32ToSeq(n as uint32) && forall i: int :: 0 <= i < suffixStartIndex ==> s[i] == 0
      ensures SeqToNat(s) == n
      decreases s, n
    {
    }
  }
}

module {:extern ""UTF8""} UTF8 {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  type ValidUTF8Bytes = i: seq<uint8>
    | ValidUTF8Seq(i)
    witness []

  function method {:extern ""Encode""} Encode(s: string): (res: Result<ValidUTF8Bytes, string>)
    ensures IsASCIIString(s) ==> res.Success? && |res.value| == |s|
    decreases s

  function method {:extern ""Decode""} Decode(b: ValidUTF8Bytes): (res: Result<string, string>)
    decreases b

  predicate method IsASCIIString(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] as int < 128
  }

  predicate method Uses1Byte(s: seq<uint8>)
    requires |s| >= 1
    decreases s
  {
    0 <= s[0] <= 127
  }

  predicate method Uses2Bytes(s: seq<uint8>)
    requires |s| >= 2
    decreases s
  {
    194 <= s[0] <= 223 &&
    128 <= s[1] <= 191
  }

  predicate method Uses3Bytes(s: seq<uint8>)
    requires |s| >= 3
    decreases s
  {
    (s[0] == 224 && 160 <= s[1] <= 191 && 128 <= s[2] <= 191) || (225 <= s[0] <= 236 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191) || (s[0] == 237 && 128 <= s[1] <= 159 && 128 <= s[2] <= 191) || (238 <= s[0] <= 239 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191)
  }

  predicate method Uses4Bytes(s: seq<uint8>)
    requires |s| >= 4
    decreases s
  {
    (s[0] == 240 && 144 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (241 <= s[0] <= 243 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (s[0] == 244 && 128 <= s[1] <= 143 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191)
  }

  predicate method {:tailrecursion} ValidUTF8Range(a: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |a|
    decreases hi - lo
  {
    if lo == hi then
      true
    else
      var r: seq<uint8> := a[lo .. hi]; if Uses1Byte(r) then ValidUTF8Range(a, lo + 1, hi) else if 2 <= |r| && Uses2Bytes(r) then ValidUTF8Range(a, lo + 2, hi) else if 3 <= |r| && Uses3Bytes(r) then ValidUTF8Range(a, lo + 3, hi) else if 4 <= |r| && Uses4Bytes(r) then ValidUTF8Range(a, lo + 4, hi) else false
  }

  lemma /*{:_induction a, b, c, lo, hi}*/ ValidUTF8Embed(a: seq<uint8>, b: seq<uint8>, c: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |b|
    ensures ValidUTF8Range(b, lo, hi) == ValidUTF8Range(a + b + c, |a| + lo, |a| + hi)
    decreases hi - lo
  {
  }

  predicate method ValidUTF8Seq(s: seq<uint8>)
    decreases s
  {
    ValidUTF8Range(s, 0, |s|)
  }

  lemma ValidUTF8Concat(s: seq<uint8>, t: seq<uint8>)
    requires ValidUTF8Seq(s) && ValidUTF8Seq(t)
    ensures ValidUTF8Seq(s + t)
    decreases s, t
  {
  }
}

module Wrappers {
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function method Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
      decreases this
    {
      match this
      case Success(s) =>
        Success(s)
      case Failure(e) =>
        Failure(reWrap(e))
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate method IsFailure()
      decreases this
    {
      Fail?
    }

    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }

  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }
}

module Com {

  module Amazonaws {

    module Kms refines ComAmazonawsKmsAbstract {
      function method DefaultKMSClientConfigType(): KMSClientConfigType
      {
        KMSClientConfigType
      }

      method {:extern} KMSClient(config: KMSClientConfigType := DefaultKMSClientConfigType()) returns (res: Result<IKeyManagementServiceClient, Error>)
        decreases config

      import opened Wrappers

      import opened UInt = StandardLibrary.UInt

      import opened UTF8

      import opened Types = ComAmazonawsKmsTypes

      datatype KMSClientConfigType = KMSClientConfigType
    }
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i])) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m) {
        return this;
      }

      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      int startingElement = checked((int)m);
      if (startingElement == 0) {
        return this;
      }

      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero) {
        return this;
      }

      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int)lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {
  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace Wrappers_Compile {

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult();
    bool IsFailure();
    Wrappers_Compile._IOption<__U> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() { }
    public static _IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>>(Wrappers_Compile.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d).@value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile._IOption<T> _source0 = this;
      if (_source0.is_None) {
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _0___mcc_h0 = _source0.dtor_value;
        T _1_v = _0___mcc_h0;
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Success(_1_v);
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IOption<T> _this, T @default) {
      Wrappers_Compile._IOption<T> _source1 = _this;
      if (_source1.is_None) {
        return @default;
      } else {
        T _2___mcc_h0 = _source1.dtor_value;
        T _3_v = _2___mcc_h0;
        return _3_v;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers_Compile._IOption<__U> PropagateFailure<__U>() {
      return Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T @value;
    public Option_Some(T @value) {
      this.@value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_Some<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out T, out R> {
    bool is_Success { get; }
    bool is_Failure { get; }
    T dtor_value { get; }
    R dtor_error { get; }
    _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    Wrappers_Compile._IOption<T> ToOption();
    bool IsFailure();
    Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Result<T, R> : _IResult<T, R> {
    public Result() { }
    public static _IResult<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    public static _IResult<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static _IResult<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d).@value;
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d).error;
      }
    }
    public abstract _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers_Compile._IOption<T> ToOption() {
      Wrappers_Compile._IResult<T, R> _source2 = this;
      if (_source2.is_Success) {
        T _4___mcc_h0 = _source2.dtor_value;
        T _5_s = _4___mcc_h0;
        return Wrappers_Compile.Option<T>.create_Some(_5_s);
      } else {
        R _6___mcc_h1 = _source2.dtor_error;
        R _7_e = _6___mcc_h1;
        return Wrappers_Compile.Option<T>.create_None();
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IResult<T, R> _this, T @default) {
      Wrappers_Compile._IResult<T, R> _source3 = _this;
      if (_source3.is_Success) {
        T _8___mcc_h0 = _source3.dtor_value;
        T _9_s = _8___mcc_h0;
        return _9_s;
      } else {
        R _10___mcc_h1 = _source3.dtor_error;
        R _11_e = _10___mcc_h1;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public static Wrappers_Compile._IResult<T, __NewR> MapFailure<__NewR>(Wrappers_Compile._IResult<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers_Compile._IResult<T, R> _source4 = _this;
      if (_source4.is_Success) {
        T _12___mcc_h0 = _source4.dtor_value;
        T _13_s = _12___mcc_h0;
        return Wrappers_Compile.Result<T, __NewR>.create_Success(_13_s);
      } else {
        R _14___mcc_h1 = _source4.dtor_error;
        R _15_e = _14___mcc_h1;
        return Wrappers_Compile.Result<T, __NewR>.create_Failure(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_15_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T @value;
    public Result_Success(T @value) {
      this.@value = @value;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Success<T, R>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R error;
    public Result_Failure(R error) {
      this.error = error;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Failure<T, R>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() { }
    public static _IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d).error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E error;
    public Outcome_Fail(E error) {
      this.error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Fail<E>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IOutcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Wrappers_Compile.Outcome<__E>.create_Pass();
      } else {
        return Wrappers_Compile.Outcome<__E>.create_Fail(error);
      }
    }
  }
} // end of namespace Wrappers_Compile
namespace StandardLibrary_mUInt_Compile {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class posInt64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    public static readonly ulong Witness = (ulong)(BigInteger.One);
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(StandardLibrary_mUInt_Compile.posInt64.Witness);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class seq16<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class seq32<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class seq64<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class __default {
    public static bool UInt8Less(byte a, byte b)
    {
      return (a) < (b);
    }
    public static bool HasUint16Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT);
    }
    public static bool HasUint32Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT32__LIMIT);
    }
    public static bool HasUint64Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT64__LIMIT);
    }
    public static Dafny.ISequence<byte> UInt16ToSeq(ushort x) {
      byte _16_b0 = (byte)((ushort)((x) / (256)));
      byte _17_b1 = (byte)((ushort)((x) % (256)));
      return Dafny.Sequence<byte>.FromElements(_16_b0, _17_b1);
    }
    public static ushort SeqToUInt16(Dafny.ISequence<byte> s) {
      ushort _18_x0 = (ushort)(((ushort)((s).Select(BigInteger.Zero))) * (256));
      return (ushort)((_18_x0) + ((ushort)((s).Select(BigInteger.One))));
    }
    public static Dafny.ISequence<byte> UInt32ToSeq(uint x) {
      byte _19_b0 = (byte)((x) / (16777216U));
      uint _20_x0 = (x) - (((uint)(_19_b0)) * (16777216U));
      byte _21_b1 = (byte)((_20_x0) / (65536U));
      uint _22_x1 = (_20_x0) - (((uint)(_21_b1)) * (65536U));
      byte _23_b2 = (byte)((_22_x1) / (256U));
      byte _24_b3 = (byte)((_22_x1) % (256U));
      return Dafny.Sequence<byte>.FromElements(_19_b0, _21_b1, _23_b2, _24_b3);
    }
    public static uint SeqToUInt32(Dafny.ISequence<byte> s) {
      uint _25_x0 = ((uint)((s).Select(BigInteger.Zero))) * (16777216U);
      uint _26_x1 = (_25_x0) + (((uint)((s).Select(BigInteger.One))) * (65536U));
      uint _27_x2 = (_26_x1) + (((uint)((s).Select(new BigInteger(2)))) * (256U));
      return (_27_x2) + ((uint)((s).Select(new BigInteger(3))));
    }
    public static Dafny.ISequence<byte> UInt64ToSeq(ulong x) {
      byte _28_b0 = (byte)((x) / (72057594037927936UL));
      ulong _29_x0 = (x) - (((ulong)(_28_b0)) * (72057594037927936UL));
      byte _30_b1 = (byte)((_29_x0) / (281474976710656UL));
      ulong _31_x1 = (_29_x0) - (((ulong)(_30_b1)) * (281474976710656UL));
      byte _32_b2 = (byte)((_31_x1) / (1099511627776UL));
      ulong _33_x2 = (_31_x1) - (((ulong)(_32_b2)) * (1099511627776UL));
      byte _34_b3 = (byte)((_33_x2) / (4294967296UL));
      ulong _35_x3 = (_33_x2) - (((ulong)(_34_b3)) * (4294967296UL));
      byte _36_b4 = (byte)((_35_x3) / (16777216UL));
      ulong _37_x4 = (_35_x3) - (((ulong)(_36_b4)) * (16777216UL));
      byte _38_b5 = (byte)((_37_x4) / (65536UL));
      ulong _39_x5 = (_37_x4) - (((ulong)(_38_b5)) * (65536UL));
      byte _40_b6 = (byte)((_39_x5) / (256UL));
      byte _41_b7 = (byte)((_39_x5) % (256UL));
      return Dafny.Sequence<byte>.FromElements(_28_b0, _30_b1, _32_b2, _34_b3, _36_b4, _38_b5, _40_b6, _41_b7);
    }
    public static ulong SeqToUInt64(Dafny.ISequence<byte> s) {
      ulong _42_x0 = ((ulong)((s).Select(BigInteger.Zero))) * (72057594037927936UL);
      ulong _43_x1 = (_42_x0) + (((ulong)((s).Select(BigInteger.One))) * (281474976710656UL));
      ulong _44_x2 = (_43_x1) + (((ulong)((s).Select(new BigInteger(2)))) * (1099511627776UL));
      ulong _45_x3 = (_44_x2) + (((ulong)((s).Select(new BigInteger(3)))) * (4294967296UL));
      ulong _46_x4 = (_45_x3) + (((ulong)((s).Select(new BigInteger(4)))) * (16777216UL));
      ulong _47_x5 = (_46_x4) + (((ulong)((s).Select(new BigInteger(5)))) * (65536UL));
      ulong _48_x6 = (_47_x5) + (((ulong)((s).Select(new BigInteger(6)))) * (256UL));
      ulong _49_x = (_48_x6) + ((ulong)((s).Select(new BigInteger(7))));
      return _49_x;
    }
    public static BigInteger UINT16__LIMIT { get {
      return new BigInteger(65536);
    } }
    public static BigInteger UINT32__LIMIT { get {
      return new BigInteger(4294967296L);
    } }
    public static BigInteger UINT64__LIMIT { get {
      return BigInteger.Parse("18446744073709551616");
    } }
    public static BigInteger INT32__MAX__LIMIT { get {
      return new BigInteger(2147483648L);
    } }
    public static BigInteger INT64__MAX__LIMIT { get {
      return new BigInteger(9223372036854775808UL);
    } }
  }
} // end of namespace StandardLibrary_mUInt_Compile
namespace StandardLibrary_Compile {

  public partial class __default {
    public static Dafny.ISequence<__T> Join<__T>(Dafny.ISequence<Dafny.ISequence<__T>> ss, Dafny.ISequence<__T> joiner)
    {
      Dafny.ISequence<__T> _50___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ss).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<__T>.Concat(_50___accumulator, (ss).Select(BigInteger.Zero));
      } else {
        _50___accumulator = Dafny.Sequence<__T>.Concat(_50___accumulator, Dafny.Sequence<__T>.Concat((ss).Select(BigInteger.Zero), joiner));
        Dafny.ISequence<Dafny.ISequence<__T>> _in0 = (ss).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in1 = joiner;
        ss = _in0;
        joiner = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> Split<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _51___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      Wrappers_Compile._IOption<BigInteger> _52_i = StandardLibrary_Compile.__default.FindIndexMatching<__T>(s, delim, BigInteger.Zero);
      if ((_52_i).is_Some) {
        _51___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_51___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements((s).Take((_52_i).dtor_value)));
        Dafny.ISequence<__T> _in2 = (s).Drop(((_52_i).dtor_value) + (BigInteger.One));
        __T _in3 = delim;
        s = _in2;
        delim = _in3;
        goto TAIL_CALL_START;
      } else {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_51___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(s));
      }
    }
    public static Wrappers_Compile._IOption<BigInteger> FindIndexMatching<__T>(Dafny.ISequence<__T> s, __T c, BigInteger i)
    {
      return StandardLibrary_Compile.__default.FindIndex<__T>(s, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_53_c) => ((System.Func<__T, bool>)((_54_x) => {
        return object.Equals(_54_x, _53_c);
      })))(c), i);
    }
    public static Wrappers_Compile._IOption<BigInteger> FindIndex<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f, BigInteger i)
    {
    TAIL_CALL_START: ;
      if ((i) == (new BigInteger((s).Count))) {
        return Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(i))) {
        return Wrappers_Compile.Option<BigInteger>.create_Some(i);
      } else {
        Dafny.ISequence<__T> _in4 = s;
        Func<__T, bool> _in5 = f;
        BigInteger _in6 = (i) + (BigInteger.One);
        s = _in4;
        f = _in5;
        i = _in6;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f)
    {
      Dafny.ISequence<__T> _55___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_55___accumulator, Dafny.Sequence<__T>.FromElements());
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(BigInteger.Zero))) {
        _55___accumulator = Dafny.Sequence<__T>.Concat(_55___accumulator, Dafny.Sequence<__T>.FromElements((s).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in7 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in8 = f;
        s = _in7;
        f = _in8;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<__T> _in9 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in10 = f;
        s = _in9;
        f = _in10;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static Dafny.ISequence<__T> Fill<__T>(__T @value, BigInteger n)
    {
      return ((System.Func<Dafny.ISequence<__T>>) (() => {
        BigInteger dim0 = n;
        var arr0 = new __T[Dafny.Helpers.ToIntChecked(dim0,"C# array size must not be larger than max 32-bit int")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _56___v0 = (BigInteger) i0;
          arr0[(int)(_56___v0)] = @value;
        }
        return Dafny.Sequence<__T>.FromArray(arr0);
      }))();
    }
    public static __T[] SeqToArray<__T>(Dafny.ISequence<__T> s)
    {
      __T[] a = new __T[0];
      __T[] _nw0 = new __T[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((s).Count), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      Func<BigInteger, __T> _arrayinit0 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_57_s) => ((System.Func<BigInteger, __T>)((_58_i) => {
        return (_57_s).Select(_58_i);
      })))(s);
      for (var _arrayinit_00 = 0; _arrayinit_00 < new BigInteger(_nw0.Length); _arrayinit_00++) {
        _nw0[(int)(_arrayinit_00)] = _arrayinit0(_arrayinit_00);
      }
      a = _nw0;
      return a;
    }
    public static bool LexicographicLessOrEqual<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_59_a, _60_b, _61_less) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, (new BigInteger((_59_a).Count)) + (BigInteger.One)), false, (((_exists_var_0) => {
        BigInteger _62_k = (BigInteger)_exists_var_0;
        return (((_62_k).Sign != -1) && ((_62_k) <= (new BigInteger((_59_a).Count)))) && (StandardLibrary_Compile.__default.LexicographicLessOrEqualAux<__T>(_59_a, _60_b, _61_less, _62_k));
      }))))(a, b, less);
    }
    public static bool LexicographicLessOrEqualAux<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less, BigInteger lengthOfCommonPrefix)
    {
      return (((lengthOfCommonPrefix) <= (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<BigInteger, Dafny.ISequence<__T>, Dafny.ISequence<__T>, bool>>((_63_lengthOfCommonPrefix, _64_a, _65_b) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, _63_lengthOfCommonPrefix), true, (((_forall_var_0) => {
        BigInteger _66_i = (BigInteger)_forall_var_0;
        return !(((_66_i).Sign != -1) && ((_66_i) < (_63_lengthOfCommonPrefix))) || (object.Equals((_64_a).Select(_66_i), (_65_b).Select(_66_i)));
      }))))(lengthOfCommonPrefix, a, b))) && (((lengthOfCommonPrefix) == (new BigInteger((a).Count))) || (((lengthOfCommonPrefix) < (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<__T, __T, bool>>(less)((a).Select(lengthOfCommonPrefix), (b).Select(lengthOfCommonPrefix)))));
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> SetToOrderedSequence<__T>(Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _67___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      if ((s).Equals((Dafny.Set<Dafny.ISequence<__T>>.FromElements()))) {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_67___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements());
      } else {
        return Dafny.Helpers.Let<int, Dafny.ISequence<Dafny.ISequence<__T>>>(0, _let_dummy_0 =>  {
          Dafny.ISequence<__T> _68_a = Dafny.Sequence<__T>.Empty;
          foreach (Dafny.ISequence<__T> _assign_such_that_0 in (s).Elements) {
            _68_a = (Dafny.ISequence<__T>)_assign_such_that_0;
            if (((s).Contains((_68_a))) && (StandardLibrary_Compile.__default.IsMinimum<__T>(_68_a, s, less))) {
              goto after__ASSIGN_SUCH_THAT_0;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 348)");
        after__ASSIGN_SUCH_THAT_0: ;
          return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(_68_a), StandardLibrary_Compile.__default.SetToOrderedSequence<__T>(Dafny.Set<Dafny.ISequence<__T>>.Difference(s, Dafny.Set<Dafny.ISequence<__T>>.FromElements(_68_a)), less));
        }
        );
      }
    }
    public static bool IsMinimum<__T>(Dafny.ISequence<__T> a, Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      return ((s).Contains((a))) && (Dafny.Helpers.Id<Func<Dafny.ISet<Dafny.ISequence<__T>>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_69_s, _70_a, _71_less) => Dafny.Helpers.Quantifier<Dafny.ISequence<__T>>((_69_s).Elements, true, (((_forall_var_1) => {
        Dafny.ISequence<__T> _72_z = (Dafny.ISequence<__T>)_forall_var_1;
        return !((_69_s).Contains((_72_z))) || (StandardLibrary_Compile.__default.LexicographicLessOrEqual<__T>(_70_a, _72_z, _71_less));
      }))))(s, a, less));
    }
  }
} // end of namespace StandardLibrary_Compile
namespace UTF8 {

  public partial class ValidUTF8Bytes {
    private static readonly Dafny.ISequence<byte> Witness = Dafny.Sequence<byte>.FromElements();
    public static Dafny.ISequence<byte> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(UTF8.ValidUTF8Bytes.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsASCIIString(Dafny.ISequence<char> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_73_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_73_s).Count)), true, (((_forall_var_2) => {
        BigInteger _74_i = (BigInteger)_forall_var_2;
        return !(((_74_i).Sign != -1) && ((_74_i) < (new BigInteger((_73_s).Count)))) || ((new BigInteger((_73_s).Select(_74_i))) < (new BigInteger(128)));
      }))))(s);
    }
    public static bool Uses1Byte(Dafny.ISequence<byte> s) {
      return ((0) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (127));
    }
    public static bool Uses2Bytes(Dafny.ISequence<byte> s) {
      return (((194) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (223))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)));
    }
    public static bool Uses3Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == (224)) && (((160) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) || (((((225) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (236))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))))) || (((((s).Select(BigInteger.Zero)) == (237)) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (159)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))))) || (((((238) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (239))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))));
    }
    public static bool Uses4Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == (240)) && (((144) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191)))) || ((((((241) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (243))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191))))) || ((((((s).Select(BigInteger.Zero)) == (244)) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (143)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191))));
    }
    public static bool ValidUTF8Range(Dafny.ISequence<byte> a, BigInteger lo, BigInteger hi)
    {
    TAIL_CALL_START: ;
      if ((lo) == (hi)) {
        return true;
      } else {
        Dafny.ISequence<byte> _75_r = (a).Subsequence(lo, hi);
        if (UTF8.__default.Uses1Byte(_75_r)) {
          Dafny.ISequence<byte> _in11 = a;
          BigInteger _in12 = (lo) + (BigInteger.One);
          BigInteger _in13 = hi;
          a = _in11;
          lo = _in12;
          hi = _in13;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(2)) <= (new BigInteger((_75_r).Count))) && (UTF8.__default.Uses2Bytes(_75_r))) {
          Dafny.ISequence<byte> _in14 = a;
          BigInteger _in15 = (lo) + (new BigInteger(2));
          BigInteger _in16 = hi;
          a = _in14;
          lo = _in15;
          hi = _in16;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(3)) <= (new BigInteger((_75_r).Count))) && (UTF8.__default.Uses3Bytes(_75_r))) {
          Dafny.ISequence<byte> _in17 = a;
          BigInteger _in18 = (lo) + (new BigInteger(3));
          BigInteger _in19 = hi;
          a = _in17;
          lo = _in18;
          hi = _in19;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(4)) <= (new BigInteger((_75_r).Count))) && (UTF8.__default.Uses4Bytes(_75_r))) {
          Dafny.ISequence<byte> _in20 = a;
          BigInteger _in21 = (lo) + (new BigInteger(4));
          BigInteger _in22 = hi;
          a = _in20;
          lo = _in21;
          hi = _in22;
          goto TAIL_CALL_START;
        } else {
          return false;
        }
      }
    }
    public static bool ValidUTF8Seq(Dafny.ISequence<byte> s) {
      return UTF8.__default.ValidUTF8Range(s, BigInteger.Zero, new BigInteger((s).Count));
    }
  }
} // end of namespace UTF8
namespace ComAmazonawsKmsTypes_Compile {

  public interface _IAlgorithmSpec {
    bool is_RSAES__PKCS1__V1__5 { get; }
    bool is_RSAES__OAEP__SHA__1 { get; }
    bool is_RSAES__OAEP__SHA__256 { get; }
    _IAlgorithmSpec DowncastClone();
  }
  public abstract class AlgorithmSpec : _IAlgorithmSpec {
    public AlgorithmSpec() { }
    private static readonly _IAlgorithmSpec theDefault = create_RSAES__PKCS1__V1__5();
    public static _IAlgorithmSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IAlgorithmSpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IAlgorithmSpec>(ComAmazonawsKmsTypes_Compile.AlgorithmSpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IAlgorithmSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAlgorithmSpec create_RSAES__PKCS1__V1__5() {
      return new AlgorithmSpec_RSAES__PKCS1__V1__5();
    }
    public static _IAlgorithmSpec create_RSAES__OAEP__SHA__1() {
      return new AlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public static _IAlgorithmSpec create_RSAES__OAEP__SHA__256() {
      return new AlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public bool is_RSAES__PKCS1__V1__5 { get { return this is AlgorithmSpec_RSAES__PKCS1__V1__5; } }
    public bool is_RSAES__OAEP__SHA__1 { get { return this is AlgorithmSpec_RSAES__OAEP__SHA__1; } }
    public bool is_RSAES__OAEP__SHA__256 { get { return this is AlgorithmSpec_RSAES__OAEP__SHA__256; } }
    public static System.Collections.Generic.IEnumerable<_IAlgorithmSpec> AllSingletonConstructors {
      get {
        yield return AlgorithmSpec.create_RSAES__PKCS1__V1__5();
        yield return AlgorithmSpec.create_RSAES__OAEP__SHA__1();
        yield return AlgorithmSpec.create_RSAES__OAEP__SHA__256();
      }
    }
    public abstract _IAlgorithmSpec DowncastClone();
  }
  public class AlgorithmSpec_RSAES__PKCS1__V1__5 : AlgorithmSpec {
    public AlgorithmSpec_RSAES__PKCS1__V1__5() {
    }
    public override _IAlgorithmSpec DowncastClone() {
      if (this is _IAlgorithmSpec dt) { return dt; }
      return new AlgorithmSpec_RSAES__PKCS1__V1__5();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.AlgorithmSpec_RSAES__PKCS1__V1__5;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.AlgorithmSpec.RSAES_PKCS1_V1_5";
      return s;
    }
  }
  public class AlgorithmSpec_RSAES__OAEP__SHA__1 : AlgorithmSpec {
    public AlgorithmSpec_RSAES__OAEP__SHA__1() {
    }
    public override _IAlgorithmSpec DowncastClone() {
      if (this is _IAlgorithmSpec dt) { return dt; }
      return new AlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.AlgorithmSpec_RSAES__OAEP__SHA__1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.AlgorithmSpec.RSAES_OAEP_SHA_1";
      return s;
    }
  }
  public class AlgorithmSpec_RSAES__OAEP__SHA__256 : AlgorithmSpec {
    public AlgorithmSpec_RSAES__OAEP__SHA__256() {
    }
    public override _IAlgorithmSpec DowncastClone() {
      if (this is _IAlgorithmSpec dt) { return dt; }
      return new AlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.AlgorithmSpec_RSAES__OAEP__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.AlgorithmSpec.RSAES_OAEP_SHA_256";
      return s;
    }
  }

  public interface _IAliasListEntry {
    bool is_AliasListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasName { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasArn { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TargetKeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_LastUpdatedDate { get; }
    _IAliasListEntry DowncastClone();
  }
  public class AliasListEntry : _IAliasListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasName;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasArn;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> TargetKeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> LastUpdatedDate;
    public AliasListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasName, Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasArn, Wrappers_Compile._IOption<Dafny.ISequence<char>> TargetKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> LastUpdatedDate) {
      this.AliasName = AliasName;
      this.AliasArn = AliasArn;
      this.TargetKeyId = TargetKeyId;
      this.CreationDate = CreationDate;
      this.LastUpdatedDate = LastUpdatedDate;
    }
    public _IAliasListEntry DowncastClone() {
      if (this is _IAliasListEntry dt) { return dt; }
      return new AliasListEntry(AliasName, AliasArn, TargetKeyId, CreationDate, LastUpdatedDate);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.AliasListEntry;
      return oth != null && object.Equals(this.AliasName, oth.AliasName) && object.Equals(this.AliasArn, oth.AliasArn) && object.Equals(this.TargetKeyId, oth.TargetKeyId) && object.Equals(this.CreationDate, oth.CreationDate) && object.Equals(this.LastUpdatedDate, oth.LastUpdatedDate);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.AliasName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.AliasArn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TargetKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CreationDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.LastUpdatedDate));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.AliasListEntry.AliasListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this.AliasName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.AliasArn);
      s += ", ";
      s += Dafny.Helpers.ToString(this.TargetKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CreationDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this.LastUpdatedDate);
      s += ")";
      return s;
    }
    private static readonly _IAliasListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IAliasListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IAliasListEntry> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IAliasListEntry>(ComAmazonawsKmsTypes_Compile.AliasListEntry.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IAliasListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAliasListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasName, Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasArn, Wrappers_Compile._IOption<Dafny.ISequence<char>> TargetKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> LastUpdatedDate) {
      return new AliasListEntry(AliasName, AliasArn, TargetKeyId, CreationDate, LastUpdatedDate);
    }
    public bool is_AliasListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasName {
      get {
        return this.AliasName;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasArn {
      get {
        return this.AliasArn;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TargetKeyId {
      get {
        return this.TargetKeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this.CreationDate;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_LastUpdatedDate {
      get {
        return this.LastUpdatedDate;
      }
    }
  }

  public partial class AliasNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ArnType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ICancelKeyDeletionRequest {
    bool is_CancelKeyDeletionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _ICancelKeyDeletionRequest DowncastClone();
  }
  public class CancelKeyDeletionRequest : _ICancelKeyDeletionRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public CancelKeyDeletionRequest(Dafny.ISequence<char> KeyId) {
      this.KeyId = KeyId;
    }
    public _ICancelKeyDeletionRequest DowncastClone() {
      if (this is _ICancelKeyDeletionRequest dt) { return dt; }
      return new CancelKeyDeletionRequest(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CancelKeyDeletionRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CancelKeyDeletionRequest.CancelKeyDeletionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _ICancelKeyDeletionRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _ICancelKeyDeletionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionRequest>(ComAmazonawsKmsTypes_Compile.CancelKeyDeletionRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICancelKeyDeletionRequest create(Dafny.ISequence<char> KeyId) {
      return new CancelKeyDeletionRequest(KeyId);
    }
    public bool is_CancelKeyDeletionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _ICancelKeyDeletionResponse {
    bool is_CancelKeyDeletionResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    _ICancelKeyDeletionResponse DowncastClone();
  }
  public class CancelKeyDeletionResponse : _ICancelKeyDeletionResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public CancelKeyDeletionResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      this.KeyId = KeyId;
    }
    public _ICancelKeyDeletionResponse DowncastClone() {
      if (this is _ICancelKeyDeletionResponse dt) { return dt; }
      return new CancelKeyDeletionResponse(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CancelKeyDeletionResponse;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CancelKeyDeletionResponse.CancelKeyDeletionResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _ICancelKeyDeletionResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _ICancelKeyDeletionResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionResponse>(ComAmazonawsKmsTypes_Compile.CancelKeyDeletionResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICancelKeyDeletionResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return new CancelKeyDeletionResponse(KeyId);
    }
    public bool is_CancelKeyDeletionResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public partial class CiphertextType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class CloudHsmClusterIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IConnectCustomKeyStoreRequest {
    bool is_ConnectCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    _IConnectCustomKeyStoreRequest DowncastClone();
  }
  public class ConnectCustomKeyStoreRequest : _IConnectCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> CustomKeyStoreId;
    public ConnectCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      this.CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IConnectCustomKeyStoreRequest DowncastClone() {
      if (this is _IConnectCustomKeyStoreRequest dt) { return dt; }
      return new ConnectCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectCustomKeyStoreRequest;
      return oth != null && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectCustomKeyStoreRequest.ConnectCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly _IConnectCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IConnectCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreRequest>(ComAmazonawsKmsTypes_Compile.ConnectCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId) {
      return new ConnectCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public bool is_ConnectCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
  }

  public interface _IConnectCustomKeyStoreResponse {
    bool is_ConnectCustomKeyStoreResponse { get; }
    _IConnectCustomKeyStoreResponse DowncastClone();
  }
  public class ConnectCustomKeyStoreResponse : _IConnectCustomKeyStoreResponse {
    public ConnectCustomKeyStoreResponse() {
    }
    public _IConnectCustomKeyStoreResponse DowncastClone() {
      if (this is _IConnectCustomKeyStoreResponse dt) { return dt; }
      return new ConnectCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectCustomKeyStoreResponse.ConnectCustomKeyStoreResponse";
      return s;
    }
    private static readonly _IConnectCustomKeyStoreResponse theDefault = create();
    public static _IConnectCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreResponse>(ComAmazonawsKmsTypes_Compile.ConnectCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectCustomKeyStoreResponse create() {
      return new ConnectCustomKeyStoreResponse();
    }
    public bool is_ConnectCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IConnectCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return ConnectCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IConnectionErrorCodeType {
    bool is_INVALID__CREDENTIALS { get; }
    bool is_CLUSTER__NOT__FOUND { get; }
    bool is_NETWORK__ERRORS { get; }
    bool is_INTERNAL__ERROR { get; }
    bool is_INSUFFICIENT__CLOUDHSM__HSMS { get; }
    bool is_USER__LOCKED__OUT { get; }
    bool is_USER__NOT__FOUND { get; }
    bool is_USER__LOGGED__IN { get; }
    bool is_SUBNET__NOT__FOUND { get; }
    _IConnectionErrorCodeType DowncastClone();
  }
  public abstract class ConnectionErrorCodeType : _IConnectionErrorCodeType {
    public ConnectionErrorCodeType() { }
    private static readonly _IConnectionErrorCodeType theDefault = create_INVALID__CREDENTIALS();
    public static _IConnectionErrorCodeType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType>(ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectionErrorCodeType create_INVALID__CREDENTIALS() {
      return new ConnectionErrorCodeType_INVALID__CREDENTIALS();
    }
    public static _IConnectionErrorCodeType create_CLUSTER__NOT__FOUND() {
      return new ConnectionErrorCodeType_CLUSTER__NOT__FOUND();
    }
    public static _IConnectionErrorCodeType create_NETWORK__ERRORS() {
      return new ConnectionErrorCodeType_NETWORK__ERRORS();
    }
    public static _IConnectionErrorCodeType create_INTERNAL__ERROR() {
      return new ConnectionErrorCodeType_INTERNAL__ERROR();
    }
    public static _IConnectionErrorCodeType create_INSUFFICIENT__CLOUDHSM__HSMS() {
      return new ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS();
    }
    public static _IConnectionErrorCodeType create_USER__LOCKED__OUT() {
      return new ConnectionErrorCodeType_USER__LOCKED__OUT();
    }
    public static _IConnectionErrorCodeType create_USER__NOT__FOUND() {
      return new ConnectionErrorCodeType_USER__NOT__FOUND();
    }
    public static _IConnectionErrorCodeType create_USER__LOGGED__IN() {
      return new ConnectionErrorCodeType_USER__LOGGED__IN();
    }
    public static _IConnectionErrorCodeType create_SUBNET__NOT__FOUND() {
      return new ConnectionErrorCodeType_SUBNET__NOT__FOUND();
    }
    public bool is_INVALID__CREDENTIALS { get { return this is ConnectionErrorCodeType_INVALID__CREDENTIALS; } }
    public bool is_CLUSTER__NOT__FOUND { get { return this is ConnectionErrorCodeType_CLUSTER__NOT__FOUND; } }
    public bool is_NETWORK__ERRORS { get { return this is ConnectionErrorCodeType_NETWORK__ERRORS; } }
    public bool is_INTERNAL__ERROR { get { return this is ConnectionErrorCodeType_INTERNAL__ERROR; } }
    public bool is_INSUFFICIENT__CLOUDHSM__HSMS { get { return this is ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS; } }
    public bool is_USER__LOCKED__OUT { get { return this is ConnectionErrorCodeType_USER__LOCKED__OUT; } }
    public bool is_USER__NOT__FOUND { get { return this is ConnectionErrorCodeType_USER__NOT__FOUND; } }
    public bool is_USER__LOGGED__IN { get { return this is ConnectionErrorCodeType_USER__LOGGED__IN; } }
    public bool is_SUBNET__NOT__FOUND { get { return this is ConnectionErrorCodeType_SUBNET__NOT__FOUND; } }
    public static System.Collections.Generic.IEnumerable<_IConnectionErrorCodeType> AllSingletonConstructors {
      get {
        yield return ConnectionErrorCodeType.create_INVALID__CREDENTIALS();
        yield return ConnectionErrorCodeType.create_CLUSTER__NOT__FOUND();
        yield return ConnectionErrorCodeType.create_NETWORK__ERRORS();
        yield return ConnectionErrorCodeType.create_INTERNAL__ERROR();
        yield return ConnectionErrorCodeType.create_INSUFFICIENT__CLOUDHSM__HSMS();
        yield return ConnectionErrorCodeType.create_USER__LOCKED__OUT();
        yield return ConnectionErrorCodeType.create_USER__NOT__FOUND();
        yield return ConnectionErrorCodeType.create_USER__LOGGED__IN();
        yield return ConnectionErrorCodeType.create_SUBNET__NOT__FOUND();
      }
    }
    public abstract _IConnectionErrorCodeType DowncastClone();
  }
  public class ConnectionErrorCodeType_INVALID__CREDENTIALS : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_INVALID__CREDENTIALS() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_INVALID__CREDENTIALS();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_INVALID__CREDENTIALS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.INVALID_CREDENTIALS";
      return s;
    }
  }
  public class ConnectionErrorCodeType_CLUSTER__NOT__FOUND : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_CLUSTER__NOT__FOUND() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_CLUSTER__NOT__FOUND();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_CLUSTER__NOT__FOUND;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.CLUSTER_NOT_FOUND";
      return s;
    }
  }
  public class ConnectionErrorCodeType_NETWORK__ERRORS : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_NETWORK__ERRORS() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_NETWORK__ERRORS();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_NETWORK__ERRORS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.NETWORK_ERRORS";
      return s;
    }
  }
  public class ConnectionErrorCodeType_INTERNAL__ERROR : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_INTERNAL__ERROR() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_INTERNAL__ERROR();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_INTERNAL__ERROR;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.INTERNAL_ERROR";
      return s;
    }
  }
  public class ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS";
      return s;
    }
  }
  public class ConnectionErrorCodeType_USER__LOCKED__OUT : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_USER__LOCKED__OUT() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_USER__LOCKED__OUT();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_USER__LOCKED__OUT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.USER_LOCKED_OUT";
      return s;
    }
  }
  public class ConnectionErrorCodeType_USER__NOT__FOUND : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_USER__NOT__FOUND() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_USER__NOT__FOUND();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_USER__NOT__FOUND;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.USER_NOT_FOUND";
      return s;
    }
  }
  public class ConnectionErrorCodeType_USER__LOGGED__IN : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_USER__LOGGED__IN() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_USER__LOGGED__IN();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_USER__LOGGED__IN;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.USER_LOGGED_IN";
      return s;
    }
  }
  public class ConnectionErrorCodeType_SUBNET__NOT__FOUND : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_SUBNET__NOT__FOUND() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_SUBNET__NOT__FOUND();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType_SUBNET__NOT__FOUND;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionErrorCodeType.SUBNET_NOT_FOUND";
      return s;
    }
  }

  public interface _IConnectionStateType {
    bool is_CONNECTED { get; }
    bool is_CONNECTING { get; }
    bool is_FAILED { get; }
    bool is_DISCONNECTED { get; }
    bool is_DISCONNECTING { get; }
    _IConnectionStateType DowncastClone();
  }
  public abstract class ConnectionStateType : _IConnectionStateType {
    public ConnectionStateType() { }
    private static readonly _IConnectionStateType theDefault = create_CONNECTED();
    public static _IConnectionStateType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectionStateType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectionStateType>(ComAmazonawsKmsTypes_Compile.ConnectionStateType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IConnectionStateType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectionStateType create_CONNECTED() {
      return new ConnectionStateType_CONNECTED();
    }
    public static _IConnectionStateType create_CONNECTING() {
      return new ConnectionStateType_CONNECTING();
    }
    public static _IConnectionStateType create_FAILED() {
      return new ConnectionStateType_FAILED();
    }
    public static _IConnectionStateType create_DISCONNECTED() {
      return new ConnectionStateType_DISCONNECTED();
    }
    public static _IConnectionStateType create_DISCONNECTING() {
      return new ConnectionStateType_DISCONNECTING();
    }
    public bool is_CONNECTED { get { return this is ConnectionStateType_CONNECTED; } }
    public bool is_CONNECTING { get { return this is ConnectionStateType_CONNECTING; } }
    public bool is_FAILED { get { return this is ConnectionStateType_FAILED; } }
    public bool is_DISCONNECTED { get { return this is ConnectionStateType_DISCONNECTED; } }
    public bool is_DISCONNECTING { get { return this is ConnectionStateType_DISCONNECTING; } }
    public static System.Collections.Generic.IEnumerable<_IConnectionStateType> AllSingletonConstructors {
      get {
        yield return ConnectionStateType.create_CONNECTED();
        yield return ConnectionStateType.create_CONNECTING();
        yield return ConnectionStateType.create_FAILED();
        yield return ConnectionStateType.create_DISCONNECTED();
        yield return ConnectionStateType.create_DISCONNECTING();
      }
    }
    public abstract _IConnectionStateType DowncastClone();
  }
  public class ConnectionStateType_CONNECTED : ConnectionStateType {
    public ConnectionStateType_CONNECTED() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_CONNECTED();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionStateType_CONNECTED;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionStateType.CONNECTED";
      return s;
    }
  }
  public class ConnectionStateType_CONNECTING : ConnectionStateType {
    public ConnectionStateType_CONNECTING() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_CONNECTING();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionStateType_CONNECTING;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionStateType.CONNECTING";
      return s;
    }
  }
  public class ConnectionStateType_FAILED : ConnectionStateType {
    public ConnectionStateType_FAILED() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_FAILED();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionStateType_FAILED;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionStateType.FAILED";
      return s;
    }
  }
  public class ConnectionStateType_DISCONNECTED : ConnectionStateType {
    public ConnectionStateType_DISCONNECTED() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_DISCONNECTED();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionStateType_DISCONNECTED;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionStateType.DISCONNECTED";
      return s;
    }
  }
  public class ConnectionStateType_DISCONNECTING : ConnectionStateType {
    public ConnectionStateType_DISCONNECTING() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_DISCONNECTING();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ConnectionStateType_DISCONNECTING;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ConnectionStateType.DISCONNECTING";
      return s;
    }
  }

  public interface _ICreateAliasRequest {
    bool is_CreateAliasRequest { get; }
    Dafny.ISequence<char> dtor_AliasName { get; }
    Dafny.ISequence<char> dtor_TargetKeyId { get; }
    _ICreateAliasRequest DowncastClone();
  }
  public class CreateAliasRequest : _ICreateAliasRequest {
    public readonly Dafny.ISequence<char> AliasName;
    public readonly Dafny.ISequence<char> TargetKeyId;
    public CreateAliasRequest(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      this.AliasName = AliasName;
      this.TargetKeyId = TargetKeyId;
    }
    public _ICreateAliasRequest DowncastClone() {
      if (this is _ICreateAliasRequest dt) { return dt; }
      return new CreateAliasRequest(AliasName, TargetKeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CreateAliasRequest;
      return oth != null && object.Equals(this.AliasName, oth.AliasName) && object.Equals(this.TargetKeyId, oth.TargetKeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.AliasName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TargetKeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CreateAliasRequest.CreateAliasRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.AliasName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.TargetKeyId);
      s += ")";
      return s;
    }
    private static readonly _ICreateAliasRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _ICreateAliasRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateAliasRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateAliasRequest>(ComAmazonawsKmsTypes_Compile.CreateAliasRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateAliasRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateAliasRequest create(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      return new CreateAliasRequest(AliasName, TargetKeyId);
    }
    public bool is_CreateAliasRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_AliasName {
      get {
        return this.AliasName;
      }
    }
    public Dafny.ISequence<char> dtor_TargetKeyId {
      get {
        return this.TargetKeyId;
      }
    }
  }

  public interface _ICreateCustomKeyStoreRequest {
    bool is_CreateCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreName { get; }
    Dafny.ISequence<char> dtor_CloudHsmClusterId { get; }
    Dafny.ISequence<char> dtor_TrustAnchorCertificate { get; }
    Dafny.ISequence<char> dtor_KeyStorePassword { get; }
    _ICreateCustomKeyStoreRequest DowncastClone();
  }
  public class CreateCustomKeyStoreRequest : _ICreateCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> CustomKeyStoreName;
    public readonly Dafny.ISequence<char> CloudHsmClusterId;
    public readonly Dafny.ISequence<char> TrustAnchorCertificate;
    public readonly Dafny.ISequence<char> KeyStorePassword;
    public CreateCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreName, Dafny.ISequence<char> CloudHsmClusterId, Dafny.ISequence<char> TrustAnchorCertificate, Dafny.ISequence<char> KeyStorePassword) {
      this.CustomKeyStoreName = CustomKeyStoreName;
      this.CloudHsmClusterId = CloudHsmClusterId;
      this.TrustAnchorCertificate = TrustAnchorCertificate;
      this.KeyStorePassword = KeyStorePassword;
    }
    public _ICreateCustomKeyStoreRequest DowncastClone() {
      if (this is _ICreateCustomKeyStoreRequest dt) { return dt; }
      return new CreateCustomKeyStoreRequest(CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, KeyStorePassword);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CreateCustomKeyStoreRequest;
      return oth != null && object.Equals(this.CustomKeyStoreName, oth.CustomKeyStoreName) && object.Equals(this.CloudHsmClusterId, oth.CloudHsmClusterId) && object.Equals(this.TrustAnchorCertificate, oth.TrustAnchorCertificate) && object.Equals(this.KeyStorePassword, oth.KeyStorePassword);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CloudHsmClusterId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TrustAnchorCertificate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyStorePassword));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CreateCustomKeyStoreRequest.CreateCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CloudHsmClusterId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.TrustAnchorCertificate);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyStorePassword);
      s += ")";
      return s;
    }
    private static readonly _ICreateCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _ICreateCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreRequest>(ComAmazonawsKmsTypes_Compile.CreateCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreName, Dafny.ISequence<char> CloudHsmClusterId, Dafny.ISequence<char> TrustAnchorCertificate, Dafny.ISequence<char> KeyStorePassword) {
      return new CreateCustomKeyStoreRequest(CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, KeyStorePassword);
    }
    public bool is_CreateCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreName {
      get {
        return this.CustomKeyStoreName;
      }
    }
    public Dafny.ISequence<char> dtor_CloudHsmClusterId {
      get {
        return this.CloudHsmClusterId;
      }
    }
    public Dafny.ISequence<char> dtor_TrustAnchorCertificate {
      get {
        return this.TrustAnchorCertificate;
      }
    }
    public Dafny.ISequence<char> dtor_KeyStorePassword {
      get {
        return this.KeyStorePassword;
      }
    }
  }

  public interface _ICreateCustomKeyStoreResponse {
    bool is_CreateCustomKeyStoreResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    _ICreateCustomKeyStoreResponse DowncastClone();
  }
  public class CreateCustomKeyStoreResponse : _ICreateCustomKeyStoreResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId;
    public CreateCustomKeyStoreResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      this.CustomKeyStoreId = CustomKeyStoreId;
    }
    public _ICreateCustomKeyStoreResponse DowncastClone() {
      if (this is _ICreateCustomKeyStoreResponse dt) { return dt; }
      return new CreateCustomKeyStoreResponse(CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CreateCustomKeyStoreResponse;
      return oth != null && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CreateCustomKeyStoreResponse.CreateCustomKeyStoreResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly _ICreateCustomKeyStoreResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _ICreateCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreResponse>(ComAmazonawsKmsTypes_Compile.CreateCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateCustomKeyStoreResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      return new CreateCustomKeyStoreResponse(CustomKeyStoreId);
    }
    public bool is_CreateCustomKeyStoreResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
  }

  public interface _ICreateGrantRequest {
    bool is_CreateGrantRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_GranteePrincipal { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal { get; }
    Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation> dtor_Operations { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> dtor_Constraints { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name { get; }
    _ICreateGrantRequest DowncastClone();
  }
  public class CreateGrantRequest : _ICreateGrantRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<char> GranteePrincipal;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal;
    public readonly Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation> Operations;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> Constraints;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Name;
    public CreateGrantRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation> Operations, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> Constraints, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name) {
      this.KeyId = KeyId;
      this.GranteePrincipal = GranteePrincipal;
      this.RetiringPrincipal = RetiringPrincipal;
      this.Operations = Operations;
      this.Constraints = Constraints;
      this.GrantTokens = GrantTokens;
      this.Name = Name;
    }
    public _ICreateGrantRequest DowncastClone() {
      if (this is _ICreateGrantRequest dt) { return dt; }
      return new CreateGrantRequest(KeyId, GranteePrincipal, RetiringPrincipal, Operations, Constraints, GrantTokens, Name);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CreateGrantRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.GranteePrincipal, oth.GranteePrincipal) && object.Equals(this.RetiringPrincipal, oth.RetiringPrincipal) && object.Equals(this.Operations, oth.Operations) && object.Equals(this.Constraints, oth.Constraints) && object.Equals(this.GrantTokens, oth.GrantTokens) && object.Equals(this.Name, oth.Name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GranteePrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.RetiringPrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Operations));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Constraints));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CreateGrantRequest.CreateGrantRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GranteePrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this.RetiringPrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Operations);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Constraints);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Name);
      s += ")";
      return s;
    }
    private static readonly _ICreateGrantRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<ComAmazonawsKmsTypes_Compile._IGrantOperation>.Empty, Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IGrantConstraints>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _ICreateGrantRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateGrantRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateGrantRequest>(ComAmazonawsKmsTypes_Compile.CreateGrantRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateGrantRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateGrantRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation> Operations, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> Constraints, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name) {
      return new CreateGrantRequest(KeyId, GranteePrincipal, RetiringPrincipal, Operations, Constraints, GrantTokens, Name);
    }
    public bool is_CreateGrantRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_GranteePrincipal {
      get {
        return this.GranteePrincipal;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal {
      get {
        return this.RetiringPrincipal;
      }
    }
    public Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation> dtor_Operations {
      get {
        return this.Operations;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> dtor_Constraints {
      get {
        return this.Constraints;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name {
      get {
        return this.Name;
      }
    }
  }

  public interface _ICreateGrantResponse {
    bool is_CreateGrantResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    _ICreateGrantResponse DowncastClone();
  }
  public class CreateGrantResponse : _ICreateGrantResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId;
    public CreateGrantResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      this.GrantToken = GrantToken;
      this.GrantId = GrantId;
    }
    public _ICreateGrantResponse DowncastClone() {
      if (this is _ICreateGrantResponse dt) { return dt; }
      return new CreateGrantResponse(GrantToken, GrantId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CreateGrantResponse;
      return oth != null && object.Equals(this.GrantToken, oth.GrantToken) && object.Equals(this.GrantId, oth.GrantId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CreateGrantResponse.CreateGrantResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.GrantToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantId);
      s += ")";
      return s;
    }
    private static readonly _ICreateGrantResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _ICreateGrantResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateGrantResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateGrantResponse>(ComAmazonawsKmsTypes_Compile.CreateGrantResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateGrantResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateGrantResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      return new CreateGrantResponse(GrantToken, GrantId);
    }
    public bool is_CreateGrantResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken {
      get {
        return this.GrantToken;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this.GrantId;
      }
    }
  }

  public interface _ICreateKeyRequest {
    bool is_CreateKeyRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> dtor_KeyUsage { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> dtor_Origin { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_Tags { get; }
    Wrappers_Compile._IOption<bool> dtor_MultiRegion { get; }
    _ICreateKeyRequest DowncastClone();
  }
  public class CreateKeyRequest : _ICreateKeyRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Description;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> Origin;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags;
    public readonly Wrappers_Compile._IOption<bool> MultiRegion;
    public CreateKeyRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags, Wrappers_Compile._IOption<bool> MultiRegion) {
      this.Policy = Policy;
      this.Description = Description;
      this.KeyUsage = KeyUsage;
      this.CustomerMasterKeySpec = CustomerMasterKeySpec;
      this.KeySpec = KeySpec;
      this.Origin = Origin;
      this.CustomKeyStoreId = CustomKeyStoreId;
      this.BypassPolicyLockoutSafetyCheck = BypassPolicyLockoutSafetyCheck;
      this.Tags = Tags;
      this.MultiRegion = MultiRegion;
    }
    public _ICreateKeyRequest DowncastClone() {
      if (this is _ICreateKeyRequest dt) { return dt; }
      return new CreateKeyRequest(Policy, Description, KeyUsage, CustomerMasterKeySpec, KeySpec, Origin, CustomKeyStoreId, BypassPolicyLockoutSafetyCheck, Tags, MultiRegion);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CreateKeyRequest;
      return oth != null && object.Equals(this.Policy, oth.Policy) && object.Equals(this.Description, oth.Description) && object.Equals(this.KeyUsage, oth.KeyUsage) && object.Equals(this.CustomerMasterKeySpec, oth.CustomerMasterKeySpec) && object.Equals(this.KeySpec, oth.KeySpec) && object.Equals(this.Origin, oth.Origin) && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId) && object.Equals(this.BypassPolicyLockoutSafetyCheck, oth.BypassPolicyLockoutSafetyCheck) && object.Equals(this.Tags, oth.Tags) && object.Equals(this.MultiRegion, oth.MultiRegion);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Policy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyUsage));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomerMasterKeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Origin));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.BypassPolicyLockoutSafetyCheck));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Tags));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.MultiRegion));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CreateKeyRequest.CreateKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.Policy);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Description);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyUsage);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomerMasterKeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Origin);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.BypassPolicyLockoutSafetyCheck);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Tags);
      s += ", ";
      s += Dafny.Helpers.ToString(this.MultiRegion);
      s += ")";
      return s;
    }
    private static readonly _ICreateKeyRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyUsageType>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeySpec>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IOriginType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static _ICreateKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateKeyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateKeyRequest>(ComAmazonawsKmsTypes_Compile.CreateKeyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateKeyRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags, Wrappers_Compile._IOption<bool> MultiRegion) {
      return new CreateKeyRequest(Policy, Description, KeyUsage, CustomerMasterKeySpec, KeySpec, Origin, CustomKeyStoreId, BypassPolicyLockoutSafetyCheck, Tags, MultiRegion);
    }
    public bool is_CreateKeyRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy {
      get {
        return this.Policy;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description {
      get {
        return this.Description;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> dtor_KeyUsage {
      get {
        return this.KeyUsage;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec {
      get {
        return this.CustomerMasterKeySpec;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> dtor_KeySpec {
      get {
        return this.KeySpec;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> dtor_Origin {
      get {
        return this.Origin;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck {
      get {
        return this.BypassPolicyLockoutSafetyCheck;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_Tags {
      get {
        return this.Tags;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_MultiRegion {
      get {
        return this.MultiRegion;
      }
    }
  }

  public interface _ICreateKeyResponse {
    bool is_CreateKeyResponse { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> dtor_KeyMetadata { get; }
    _ICreateKeyResponse DowncastClone();
  }
  public class CreateKeyResponse : _ICreateKeyResponse {
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> KeyMetadata;
    public CreateKeyResponse(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> KeyMetadata) {
      this.KeyMetadata = KeyMetadata;
    }
    public _ICreateKeyResponse DowncastClone() {
      if (this is _ICreateKeyResponse dt) { return dt; }
      return new CreateKeyResponse(KeyMetadata);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CreateKeyResponse;
      return oth != null && object.Equals(this.KeyMetadata, oth.KeyMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CreateKeyResponse.CreateKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyMetadata);
      s += ")";
      return s;
    }
    private static readonly _ICreateKeyResponse theDefault = create(Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyMetadata>.Default());
    public static _ICreateKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateKeyResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateKeyResponse>(ComAmazonawsKmsTypes_Compile.CreateKeyResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICreateKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateKeyResponse create(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> KeyMetadata) {
      return new CreateKeyResponse(KeyMetadata);
    }
    public bool is_CreateKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> dtor_KeyMetadata {
      get {
        return this.KeyMetadata;
      }
    }
  }

  public interface _ICustomerMasterKeySpec {
    bool is_RSA__2048 { get; }
    bool is_RSA__3072 { get; }
    bool is_RSA__4096 { get; }
    bool is_ECC__NIST__P256 { get; }
    bool is_ECC__NIST__P384 { get; }
    bool is_ECC__NIST__P521 { get; }
    bool is_ECC__SECG__P256K1 { get; }
    bool is_SYMMETRIC__DEFAULT { get; }
    _ICustomerMasterKeySpec DowncastClone();
  }
  public abstract class CustomerMasterKeySpec : _ICustomerMasterKeySpec {
    public CustomerMasterKeySpec() { }
    private static readonly _ICustomerMasterKeySpec theDefault = create_RSA__2048();
    public static _ICustomerMasterKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec>(ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICustomerMasterKeySpec create_RSA__2048() {
      return new CustomerMasterKeySpec_RSA__2048();
    }
    public static _ICustomerMasterKeySpec create_RSA__3072() {
      return new CustomerMasterKeySpec_RSA__3072();
    }
    public static _ICustomerMasterKeySpec create_RSA__4096() {
      return new CustomerMasterKeySpec_RSA__4096();
    }
    public static _ICustomerMasterKeySpec create_ECC__NIST__P256() {
      return new CustomerMasterKeySpec_ECC__NIST__P256();
    }
    public static _ICustomerMasterKeySpec create_ECC__NIST__P384() {
      return new CustomerMasterKeySpec_ECC__NIST__P384();
    }
    public static _ICustomerMasterKeySpec create_ECC__NIST__P521() {
      return new CustomerMasterKeySpec_ECC__NIST__P521();
    }
    public static _ICustomerMasterKeySpec create_ECC__SECG__P256K1() {
      return new CustomerMasterKeySpec_ECC__SECG__P256K1();
    }
    public static _ICustomerMasterKeySpec create_SYMMETRIC__DEFAULT() {
      return new CustomerMasterKeySpec_SYMMETRIC__DEFAULT();
    }
    public bool is_RSA__2048 { get { return this is CustomerMasterKeySpec_RSA__2048; } }
    public bool is_RSA__3072 { get { return this is CustomerMasterKeySpec_RSA__3072; } }
    public bool is_RSA__4096 { get { return this is CustomerMasterKeySpec_RSA__4096; } }
    public bool is_ECC__NIST__P256 { get { return this is CustomerMasterKeySpec_ECC__NIST__P256; } }
    public bool is_ECC__NIST__P384 { get { return this is CustomerMasterKeySpec_ECC__NIST__P384; } }
    public bool is_ECC__NIST__P521 { get { return this is CustomerMasterKeySpec_ECC__NIST__P521; } }
    public bool is_ECC__SECG__P256K1 { get { return this is CustomerMasterKeySpec_ECC__SECG__P256K1; } }
    public bool is_SYMMETRIC__DEFAULT { get { return this is CustomerMasterKeySpec_SYMMETRIC__DEFAULT; } }
    public static System.Collections.Generic.IEnumerable<_ICustomerMasterKeySpec> AllSingletonConstructors {
      get {
        yield return CustomerMasterKeySpec.create_RSA__2048();
        yield return CustomerMasterKeySpec.create_RSA__3072();
        yield return CustomerMasterKeySpec.create_RSA__4096();
        yield return CustomerMasterKeySpec.create_ECC__NIST__P256();
        yield return CustomerMasterKeySpec.create_ECC__NIST__P384();
        yield return CustomerMasterKeySpec.create_ECC__NIST__P521();
        yield return CustomerMasterKeySpec.create_ECC__SECG__P256K1();
        yield return CustomerMasterKeySpec.create_SYMMETRIC__DEFAULT();
      }
    }
    public abstract _ICustomerMasterKeySpec DowncastClone();
  }
  public class CustomerMasterKeySpec_RSA__2048 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_RSA__2048() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_RSA__2048();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_RSA__2048;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.RSA_2048";
      return s;
    }
  }
  public class CustomerMasterKeySpec_RSA__3072 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_RSA__3072() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_RSA__3072();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_RSA__3072;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.RSA_3072";
      return s;
    }
  }
  public class CustomerMasterKeySpec_RSA__4096 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_RSA__4096() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_RSA__4096();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_RSA__4096;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.RSA_4096";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__NIST__P256 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__NIST__P256() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__NIST__P256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_ECC__NIST__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.ECC_NIST_P256";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__NIST__P384 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__NIST__P384() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__NIST__P384();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_ECC__NIST__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.ECC_NIST_P384";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__NIST__P521 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__NIST__P521() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__NIST__P521();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_ECC__NIST__P521;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.ECC_NIST_P521";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__SECG__P256K1 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__SECG__P256K1() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__SECG__P256K1();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_ECC__SECG__P256K1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.ECC_SECG_P256K1";
      return s;
    }
  }
  public class CustomerMasterKeySpec_SYMMETRIC__DEFAULT : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_SYMMETRIC__DEFAULT() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_SYMMETRIC__DEFAULT();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec_SYMMETRIC__DEFAULT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomerMasterKeySpec.SYMMETRIC_DEFAULT";
      return s;
    }
  }

  public partial class CustomKeyStoreIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class CustomKeyStoreNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ICustomKeyStoresListEntry {
    bool is_CustomKeyStoresListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TrustAnchorCertificate { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionStateType> dtor_ConnectionState { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType> dtor_ConnectionErrorCode { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    _ICustomKeyStoresListEntry DowncastClone();
  }
  public class CustomKeyStoresListEntry : _ICustomKeyStoresListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> TrustAnchorCertificate;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionStateType> ConnectionState;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType> ConnectionErrorCode;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate;
    public CustomKeyStoresListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<Dafny.ISequence<char>> TrustAnchorCertificate, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionStateType> ConnectionState, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType> ConnectionErrorCode, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate) {
      this.CustomKeyStoreId = CustomKeyStoreId;
      this.CustomKeyStoreName = CustomKeyStoreName;
      this.CloudHsmClusterId = CloudHsmClusterId;
      this.TrustAnchorCertificate = TrustAnchorCertificate;
      this.ConnectionState = ConnectionState;
      this.ConnectionErrorCode = ConnectionErrorCode;
      this.CreationDate = CreationDate;
    }
    public _ICustomKeyStoresListEntry DowncastClone() {
      if (this is _ICustomKeyStoresListEntry dt) { return dt; }
      return new CustomKeyStoresListEntry(CustomKeyStoreId, CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, ConnectionState, ConnectionErrorCode, CreationDate);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.CustomKeyStoresListEntry;
      return oth != null && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId) && object.Equals(this.CustomKeyStoreName, oth.CustomKeyStoreName) && object.Equals(this.CloudHsmClusterId, oth.CloudHsmClusterId) && object.Equals(this.TrustAnchorCertificate, oth.TrustAnchorCertificate) && object.Equals(this.ConnectionState, oth.ConnectionState) && object.Equals(this.ConnectionErrorCode, oth.ConnectionErrorCode) && object.Equals(this.CreationDate, oth.CreationDate);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CloudHsmClusterId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TrustAnchorCertificate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ConnectionState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ConnectionErrorCode));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CreationDate));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.CustomKeyStoresListEntry.CustomKeyStoresListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CloudHsmClusterId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.TrustAnchorCertificate);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ConnectionState);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ConnectionErrorCode);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CreationDate);
      s += ")";
      return s;
    }
    private static readonly _ICustomKeyStoresListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IConnectionStateType>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _ICustomKeyStoresListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry>(ComAmazonawsKmsTypes_Compile.CustomKeyStoresListEntry.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICustomKeyStoresListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<Dafny.ISequence<char>> TrustAnchorCertificate, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionStateType> ConnectionState, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType> ConnectionErrorCode, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate) {
      return new CustomKeyStoresListEntry(CustomKeyStoreId, CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, ConnectionState, ConnectionErrorCode, CreationDate);
    }
    public bool is_CustomKeyStoresListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName {
      get {
        return this.CustomKeyStoreName;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId {
      get {
        return this.CloudHsmClusterId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TrustAnchorCertificate {
      get {
        return this.TrustAnchorCertificate;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionStateType> dtor_ConnectionState {
      get {
        return this.ConnectionState;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IConnectionErrorCodeType> dtor_ConnectionErrorCode {
      get {
        return this.ConnectionErrorCode;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this.CreationDate;
      }
    }
  }

  public interface _IDataKeyPairSpec {
    bool is_RSA__2048 { get; }
    bool is_RSA__3072 { get; }
    bool is_RSA__4096 { get; }
    bool is_ECC__NIST__P256 { get; }
    bool is_ECC__NIST__P384 { get; }
    bool is_ECC__NIST__P521 { get; }
    bool is_ECC__SECG__P256K1 { get; }
    _IDataKeyPairSpec DowncastClone();
  }
  public abstract class DataKeyPairSpec : _IDataKeyPairSpec {
    public DataKeyPairSpec() { }
    private static readonly _IDataKeyPairSpec theDefault = create_RSA__2048();
    public static _IDataKeyPairSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec>(ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDataKeyPairSpec create_RSA__2048() {
      return new DataKeyPairSpec_RSA__2048();
    }
    public static _IDataKeyPairSpec create_RSA__3072() {
      return new DataKeyPairSpec_RSA__3072();
    }
    public static _IDataKeyPairSpec create_RSA__4096() {
      return new DataKeyPairSpec_RSA__4096();
    }
    public static _IDataKeyPairSpec create_ECC__NIST__P256() {
      return new DataKeyPairSpec_ECC__NIST__P256();
    }
    public static _IDataKeyPairSpec create_ECC__NIST__P384() {
      return new DataKeyPairSpec_ECC__NIST__P384();
    }
    public static _IDataKeyPairSpec create_ECC__NIST__P521() {
      return new DataKeyPairSpec_ECC__NIST__P521();
    }
    public static _IDataKeyPairSpec create_ECC__SECG__P256K1() {
      return new DataKeyPairSpec_ECC__SECG__P256K1();
    }
    public bool is_RSA__2048 { get { return this is DataKeyPairSpec_RSA__2048; } }
    public bool is_RSA__3072 { get { return this is DataKeyPairSpec_RSA__3072; } }
    public bool is_RSA__4096 { get { return this is DataKeyPairSpec_RSA__4096; } }
    public bool is_ECC__NIST__P256 { get { return this is DataKeyPairSpec_ECC__NIST__P256; } }
    public bool is_ECC__NIST__P384 { get { return this is DataKeyPairSpec_ECC__NIST__P384; } }
    public bool is_ECC__NIST__P521 { get { return this is DataKeyPairSpec_ECC__NIST__P521; } }
    public bool is_ECC__SECG__P256K1 { get { return this is DataKeyPairSpec_ECC__SECG__P256K1; } }
    public static System.Collections.Generic.IEnumerable<_IDataKeyPairSpec> AllSingletonConstructors {
      get {
        yield return DataKeyPairSpec.create_RSA__2048();
        yield return DataKeyPairSpec.create_RSA__3072();
        yield return DataKeyPairSpec.create_RSA__4096();
        yield return DataKeyPairSpec.create_ECC__NIST__P256();
        yield return DataKeyPairSpec.create_ECC__NIST__P384();
        yield return DataKeyPairSpec.create_ECC__NIST__P521();
        yield return DataKeyPairSpec.create_ECC__SECG__P256K1();
      }
    }
    public abstract _IDataKeyPairSpec DowncastClone();
  }
  public class DataKeyPairSpec_RSA__2048 : DataKeyPairSpec {
    public DataKeyPairSpec_RSA__2048() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_RSA__2048();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeyPairSpec_RSA__2048;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.RSA_2048";
      return s;
    }
  }
  public class DataKeyPairSpec_RSA__3072 : DataKeyPairSpec {
    public DataKeyPairSpec_RSA__3072() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_RSA__3072();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeyPairSpec_RSA__3072;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.RSA_3072";
      return s;
    }
  }
  public class DataKeyPairSpec_RSA__4096 : DataKeyPairSpec {
    public DataKeyPairSpec_RSA__4096() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_RSA__4096();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeyPairSpec_RSA__4096;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.RSA_4096";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__NIST__P256 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__NIST__P256() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__NIST__P256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeyPairSpec_ECC__NIST__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.ECC_NIST_P256";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__NIST__P384 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__NIST__P384() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__NIST__P384();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeyPairSpec_ECC__NIST__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.ECC_NIST_P384";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__NIST__P521 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__NIST__P521() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__NIST__P521();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeyPairSpec_ECC__NIST__P521;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.ECC_NIST_P521";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__SECG__P256K1 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__SECG__P256K1() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__SECG__P256K1();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeyPairSpec_ECC__SECG__P256K1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.ECC_SECG_P256K1";
      return s;
    }
  }

  public interface _IDataKeySpec {
    bool is_AES__256 { get; }
    bool is_AES__128 { get; }
    _IDataKeySpec DowncastClone();
  }
  public abstract class DataKeySpec : _IDataKeySpec {
    public DataKeySpec() { }
    private static readonly _IDataKeySpec theDefault = create_AES__256();
    public static _IDataKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDataKeySpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDataKeySpec>(ComAmazonawsKmsTypes_Compile.DataKeySpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDataKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDataKeySpec create_AES__256() {
      return new DataKeySpec_AES__256();
    }
    public static _IDataKeySpec create_AES__128() {
      return new DataKeySpec_AES__128();
    }
    public bool is_AES__256 { get { return this is DataKeySpec_AES__256; } }
    public bool is_AES__128 { get { return this is DataKeySpec_AES__128; } }
    public static System.Collections.Generic.IEnumerable<_IDataKeySpec> AllSingletonConstructors {
      get {
        yield return DataKeySpec.create_AES__256();
        yield return DataKeySpec.create_AES__128();
      }
    }
    public abstract _IDataKeySpec DowncastClone();
  }
  public class DataKeySpec_AES__256 : DataKeySpec {
    public DataKeySpec_AES__256() {
    }
    public override _IDataKeySpec DowncastClone() {
      if (this is _IDataKeySpec dt) { return dt; }
      return new DataKeySpec_AES__256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeySpec_AES__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeySpec.AES_256";
      return s;
    }
  }
  public class DataKeySpec_AES__128 : DataKeySpec {
    public DataKeySpec_AES__128() {
    }
    public override _IDataKeySpec DowncastClone() {
      if (this is _IDataKeySpec dt) { return dt; }
      return new DataKeySpec_AES__128();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DataKeySpec_AES__128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DataKeySpec.AES_128";
      return s;
    }
  }

  public interface _IDecryptRequest {
    bool is_DecryptRequest { get; }
    Dafny.ISequence<byte> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IDecryptRequest DowncastClone();
  }
  public class DecryptRequest : _IDecryptRequest {
    public readonly Dafny.ISequence<byte> CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm;
    public DecryptRequest(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this.CiphertextBlob = CiphertextBlob;
      this.EncryptionContext = EncryptionContext;
      this.GrantTokens = GrantTokens;
      this.KeyId = KeyId;
      this.EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IDecryptRequest DowncastClone() {
      if (this is _IDecryptRequest dt) { return dt; }
      return new DecryptRequest(CiphertextBlob, EncryptionContext, GrantTokens, KeyId, EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DecryptRequest;
      return oth != null && object.Equals(this.CiphertextBlob, oth.CiphertextBlob) && object.Equals(this.EncryptionContext, oth.EncryptionContext) && object.Equals(this.GrantTokens, oth.GrantTokens) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.EncryptionAlgorithm, oth.EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DecryptRequest.DecryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _IDecryptRequest theDefault = create(Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default());
    public static _IDecryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDecryptRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDecryptRequest>(ComAmazonawsKmsTypes_Compile.DecryptRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDecryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecryptRequest create(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new DecryptRequest(CiphertextBlob, EncryptionContext, GrantTokens, KeyId, EncryptionAlgorithm);
    }
    public bool is_DecryptRequest { get { return true; } }
    public Dafny.ISequence<byte> dtor_CiphertextBlob {
      get {
        return this.CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this.EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this.EncryptionAlgorithm;
      }
    }
  }

  public interface _IDecryptResponse {
    bool is_DecryptResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IDecryptResponse DowncastClone();
  }
  public class DecryptResponse : _IDecryptResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm;
    public DecryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this.KeyId = KeyId;
      this.Plaintext = Plaintext;
      this.EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IDecryptResponse DowncastClone() {
      if (this is _IDecryptResponse dt) { return dt; }
      return new DecryptResponse(KeyId, Plaintext, EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DecryptResponse;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Plaintext, oth.Plaintext) && object.Equals(this.EncryptionAlgorithm, oth.EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DecryptResponse.DecryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _IDecryptResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default());
    public static _IDecryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDecryptResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDecryptResponse>(ComAmazonawsKmsTypes_Compile.DecryptResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDecryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecryptResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new DecryptResponse(KeyId, Plaintext, EncryptionAlgorithm);
    }
    public bool is_DecryptResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext {
      get {
        return this.Plaintext;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this.EncryptionAlgorithm;
      }
    }
  }

  public interface _IDeleteAliasRequest {
    bool is_DeleteAliasRequest { get; }
    Dafny.ISequence<char> dtor_AliasName { get; }
    _IDeleteAliasRequest DowncastClone();
  }
  public class DeleteAliasRequest : _IDeleteAliasRequest {
    public readonly Dafny.ISequence<char> AliasName;
    public DeleteAliasRequest(Dafny.ISequence<char> AliasName) {
      this.AliasName = AliasName;
    }
    public _IDeleteAliasRequest DowncastClone() {
      if (this is _IDeleteAliasRequest dt) { return dt; }
      return new DeleteAliasRequest(AliasName);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DeleteAliasRequest;
      return oth != null && object.Equals(this.AliasName, oth.AliasName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.AliasName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DeleteAliasRequest.DeleteAliasRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.AliasName);
      s += ")";
      return s;
    }
    private static readonly _IDeleteAliasRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IDeleteAliasRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteAliasRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteAliasRequest>(ComAmazonawsKmsTypes_Compile.DeleteAliasRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteAliasRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteAliasRequest create(Dafny.ISequence<char> AliasName) {
      return new DeleteAliasRequest(AliasName);
    }
    public bool is_DeleteAliasRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_AliasName {
      get {
        return this.AliasName;
      }
    }
  }

  public interface _IDeleteCustomKeyStoreRequest {
    bool is_DeleteCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    _IDeleteCustomKeyStoreRequest DowncastClone();
  }
  public class DeleteCustomKeyStoreRequest : _IDeleteCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> CustomKeyStoreId;
    public DeleteCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      this.CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IDeleteCustomKeyStoreRequest DowncastClone() {
      if (this is _IDeleteCustomKeyStoreRequest dt) { return dt; }
      return new DeleteCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DeleteCustomKeyStoreRequest;
      return oth != null && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DeleteCustomKeyStoreRequest.DeleteCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly _IDeleteCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IDeleteCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreRequest>(ComAmazonawsKmsTypes_Compile.DeleteCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId) {
      return new DeleteCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public bool is_DeleteCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
  }

  public interface _IDeleteCustomKeyStoreResponse {
    bool is_DeleteCustomKeyStoreResponse { get; }
    _IDeleteCustomKeyStoreResponse DowncastClone();
  }
  public class DeleteCustomKeyStoreResponse : _IDeleteCustomKeyStoreResponse {
    public DeleteCustomKeyStoreResponse() {
    }
    public _IDeleteCustomKeyStoreResponse DowncastClone() {
      if (this is _IDeleteCustomKeyStoreResponse dt) { return dt; }
      return new DeleteCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DeleteCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DeleteCustomKeyStoreResponse.DeleteCustomKeyStoreResponse";
      return s;
    }
    private static readonly _IDeleteCustomKeyStoreResponse theDefault = create();
    public static _IDeleteCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreResponse>(ComAmazonawsKmsTypes_Compile.DeleteCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteCustomKeyStoreResponse create() {
      return new DeleteCustomKeyStoreResponse();
    }
    public bool is_DeleteCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IDeleteCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return DeleteCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IDeleteImportedKeyMaterialRequest {
    bool is_DeleteImportedKeyMaterialRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IDeleteImportedKeyMaterialRequest DowncastClone();
  }
  public class DeleteImportedKeyMaterialRequest : _IDeleteImportedKeyMaterialRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public DeleteImportedKeyMaterialRequest(Dafny.ISequence<char> KeyId) {
      this.KeyId = KeyId;
    }
    public _IDeleteImportedKeyMaterialRequest DowncastClone() {
      if (this is _IDeleteImportedKeyMaterialRequest dt) { return dt; }
      return new DeleteImportedKeyMaterialRequest(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DeleteImportedKeyMaterialRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DeleteImportedKeyMaterialRequest.DeleteImportedKeyMaterialRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IDeleteImportedKeyMaterialRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IDeleteImportedKeyMaterialRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteImportedKeyMaterialRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteImportedKeyMaterialRequest>(ComAmazonawsKmsTypes_Compile.DeleteImportedKeyMaterialRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDeleteImportedKeyMaterialRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteImportedKeyMaterialRequest create(Dafny.ISequence<char> KeyId) {
      return new DeleteImportedKeyMaterialRequest(KeyId);
    }
    public bool is_DeleteImportedKeyMaterialRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IDescribeCustomKeyStoresRequest {
    bool is_DescribeCustomKeyStoresRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IDescribeCustomKeyStoresRequest DowncastClone();
  }
  public class DescribeCustomKeyStoresRequest : _IDescribeCustomKeyStoresRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName;
    public readonly Wrappers_Compile._IOption<int> Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker;
    public DescribeCustomKeyStoresRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this.CustomKeyStoreId = CustomKeyStoreId;
      this.CustomKeyStoreName = CustomKeyStoreName;
      this.Limit = Limit;
      this.Marker = Marker;
    }
    public _IDescribeCustomKeyStoresRequest DowncastClone() {
      if (this is _IDescribeCustomKeyStoresRequest dt) { return dt; }
      return new DescribeCustomKeyStoresRequest(CustomKeyStoreId, CustomKeyStoreName, Limit, Marker);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DescribeCustomKeyStoresRequest;
      return oth != null && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId) && object.Equals(this.CustomKeyStoreName, oth.CustomKeyStoreName) && object.Equals(this.Limit, oth.Limit) && object.Equals(this.Marker, oth.Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DescribeCustomKeyStoresRequest.DescribeCustomKeyStoresRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Marker);
      s += ")";
      return s;
    }
    private static readonly _IDescribeCustomKeyStoresRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IDescribeCustomKeyStoresRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresRequest>(ComAmazonawsKmsTypes_Compile.DescribeCustomKeyStoresRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeCustomKeyStoresRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new DescribeCustomKeyStoresRequest(CustomKeyStoreId, CustomKeyStoreName, Limit, Marker);
    }
    public bool is_DescribeCustomKeyStoresRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName {
      get {
        return this.CustomKeyStoreName;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this.Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this.Marker;
      }
    }
  }

  public interface _IDescribeCustomKeyStoresResponse {
    bool is_DescribeCustomKeyStoresResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry>> dtor_CustomKeyStores { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IDescribeCustomKeyStoresResponse DowncastClone();
  }
  public class DescribeCustomKeyStoresResponse : _IDescribeCustomKeyStoresResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry>> CustomKeyStores;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker;
    public readonly Wrappers_Compile._IOption<bool> Truncated;
    public DescribeCustomKeyStoresResponse(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry>> CustomKeyStores, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this.CustomKeyStores = CustomKeyStores;
      this.NextMarker = NextMarker;
      this.Truncated = Truncated;
    }
    public _IDescribeCustomKeyStoresResponse DowncastClone() {
      if (this is _IDescribeCustomKeyStoresResponse dt) { return dt; }
      return new DescribeCustomKeyStoresResponse(CustomKeyStores, NextMarker, Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DescribeCustomKeyStoresResponse;
      return oth != null && object.Equals(this.CustomKeyStores, oth.CustomKeyStores) && object.Equals(this.NextMarker, oth.NextMarker) && object.Equals(this.Truncated, oth.Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStores));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DescribeCustomKeyStoresResponse.DescribeCustomKeyStoresResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStores);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Truncated);
      s += ")";
      return s;
    }
    private static readonly _IDescribeCustomKeyStoresResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static _IDescribeCustomKeyStoresResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresResponse>(ComAmazonawsKmsTypes_Compile.DescribeCustomKeyStoresResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeCustomKeyStoresResponse create(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry>> CustomKeyStores, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new DescribeCustomKeyStoresResponse(CustomKeyStores, NextMarker, Truncated);
    }
    public bool is_DescribeCustomKeyStoresResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ICustomKeyStoresListEntry>> dtor_CustomKeyStores {
      get {
        return this.CustomKeyStores;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this.NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this.Truncated;
      }
    }
  }

  public interface _IDescribeKeyRequest {
    bool is_DescribeKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IDescribeKeyRequest DowncastClone();
  }
  public class DescribeKeyRequest : _IDescribeKeyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public DescribeKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.KeyId = KeyId;
      this.GrantTokens = GrantTokens;
    }
    public _IDescribeKeyRequest DowncastClone() {
      if (this is _IDescribeKeyRequest dt) { return dt; }
      return new DescribeKeyRequest(KeyId, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DescribeKeyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DescribeKeyRequest.DescribeKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IDescribeKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IDescribeKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeKeyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeKeyRequest>(ComAmazonawsKmsTypes_Compile.DescribeKeyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeKeyRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new DescribeKeyRequest(KeyId, GrantTokens);
    }
    public bool is_DescribeKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IDescribeKeyResponse {
    bool is_DescribeKeyResponse { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> dtor_KeyMetadata { get; }
    _IDescribeKeyResponse DowncastClone();
  }
  public class DescribeKeyResponse : _IDescribeKeyResponse {
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> KeyMetadata;
    public DescribeKeyResponse(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> KeyMetadata) {
      this.KeyMetadata = KeyMetadata;
    }
    public _IDescribeKeyResponse DowncastClone() {
      if (this is _IDescribeKeyResponse dt) { return dt; }
      return new DescribeKeyResponse(KeyMetadata);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DescribeKeyResponse;
      return oth != null && object.Equals(this.KeyMetadata, oth.KeyMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DescribeKeyResponse.DescribeKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyMetadata);
      s += ")";
      return s;
    }
    private static readonly _IDescribeKeyResponse theDefault = create(Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyMetadata>.Default());
    public static _IDescribeKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeKeyResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeKeyResponse>(ComAmazonawsKmsTypes_Compile.DescribeKeyResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDescribeKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeKeyResponse create(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> KeyMetadata) {
      return new DescribeKeyResponse(KeyMetadata);
    }
    public bool is_DescribeKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> dtor_KeyMetadata {
      get {
        return this.KeyMetadata;
      }
    }
  }

  public partial class DescriptionType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IDisableKeyRequest {
    bool is_DisableKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IDisableKeyRequest DowncastClone();
  }
  public class DisableKeyRequest : _IDisableKeyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public DisableKeyRequest(Dafny.ISequence<char> KeyId) {
      this.KeyId = KeyId;
    }
    public _IDisableKeyRequest DowncastClone() {
      if (this is _IDisableKeyRequest dt) { return dt; }
      return new DisableKeyRequest(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DisableKeyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DisableKeyRequest.DisableKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IDisableKeyRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IDisableKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisableKeyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisableKeyRequest>(ComAmazonawsKmsTypes_Compile.DisableKeyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisableKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisableKeyRequest create(Dafny.ISequence<char> KeyId) {
      return new DisableKeyRequest(KeyId);
    }
    public bool is_DisableKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IDisableKeyRotationRequest {
    bool is_DisableKeyRotationRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IDisableKeyRotationRequest DowncastClone();
  }
  public class DisableKeyRotationRequest : _IDisableKeyRotationRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public DisableKeyRotationRequest(Dafny.ISequence<char> KeyId) {
      this.KeyId = KeyId;
    }
    public _IDisableKeyRotationRequest DowncastClone() {
      if (this is _IDisableKeyRotationRequest dt) { return dt; }
      return new DisableKeyRotationRequest(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DisableKeyRotationRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DisableKeyRotationRequest.DisableKeyRotationRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IDisableKeyRotationRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IDisableKeyRotationRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisableKeyRotationRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisableKeyRotationRequest>(ComAmazonawsKmsTypes_Compile.DisableKeyRotationRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisableKeyRotationRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisableKeyRotationRequest create(Dafny.ISequence<char> KeyId) {
      return new DisableKeyRotationRequest(KeyId);
    }
    public bool is_DisableKeyRotationRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IDisconnectCustomKeyStoreRequest {
    bool is_DisconnectCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    _IDisconnectCustomKeyStoreRequest DowncastClone();
  }
  public class DisconnectCustomKeyStoreRequest : _IDisconnectCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> CustomKeyStoreId;
    public DisconnectCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      this.CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IDisconnectCustomKeyStoreRequest DowncastClone() {
      if (this is _IDisconnectCustomKeyStoreRequest dt) { return dt; }
      return new DisconnectCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DisconnectCustomKeyStoreRequest;
      return oth != null && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DisconnectCustomKeyStoreRequest.DisconnectCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly _IDisconnectCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IDisconnectCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreRequest>(ComAmazonawsKmsTypes_Compile.DisconnectCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisconnectCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId) {
      return new DisconnectCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public bool is_DisconnectCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
  }

  public interface _IDisconnectCustomKeyStoreResponse {
    bool is_DisconnectCustomKeyStoreResponse { get; }
    _IDisconnectCustomKeyStoreResponse DowncastClone();
  }
  public class DisconnectCustomKeyStoreResponse : _IDisconnectCustomKeyStoreResponse {
    public DisconnectCustomKeyStoreResponse() {
    }
    public _IDisconnectCustomKeyStoreResponse DowncastClone() {
      if (this is _IDisconnectCustomKeyStoreResponse dt) { return dt; }
      return new DisconnectCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.DisconnectCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.DisconnectCustomKeyStoreResponse.DisconnectCustomKeyStoreResponse";
      return s;
    }
    private static readonly _IDisconnectCustomKeyStoreResponse theDefault = create();
    public static _IDisconnectCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreResponse>(ComAmazonawsKmsTypes_Compile.DisconnectCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisconnectCustomKeyStoreResponse create() {
      return new DisconnectCustomKeyStoreResponse();
    }
    public bool is_DisconnectCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IDisconnectCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return DisconnectCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IEnableKeyRequest {
    bool is_EnableKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IEnableKeyRequest DowncastClone();
  }
  public class EnableKeyRequest : _IEnableKeyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public EnableKeyRequest(Dafny.ISequence<char> KeyId) {
      this.KeyId = KeyId;
    }
    public _IEnableKeyRequest DowncastClone() {
      if (this is _IEnableKeyRequest dt) { return dt; }
      return new EnableKeyRequest(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.EnableKeyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.EnableKeyRequest.EnableKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IEnableKeyRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IEnableKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEnableKeyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEnableKeyRequest>(ComAmazonawsKmsTypes_Compile.EnableKeyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEnableKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnableKeyRequest create(Dafny.ISequence<char> KeyId) {
      return new EnableKeyRequest(KeyId);
    }
    public bool is_EnableKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IEnableKeyRotationRequest {
    bool is_EnableKeyRotationRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IEnableKeyRotationRequest DowncastClone();
  }
  public class EnableKeyRotationRequest : _IEnableKeyRotationRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public EnableKeyRotationRequest(Dafny.ISequence<char> KeyId) {
      this.KeyId = KeyId;
    }
    public _IEnableKeyRotationRequest DowncastClone() {
      if (this is _IEnableKeyRotationRequest dt) { return dt; }
      return new EnableKeyRotationRequest(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.EnableKeyRotationRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.EnableKeyRotationRequest.EnableKeyRotationRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IEnableKeyRotationRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IEnableKeyRotationRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEnableKeyRotationRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEnableKeyRotationRequest>(ComAmazonawsKmsTypes_Compile.EnableKeyRotationRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEnableKeyRotationRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnableKeyRotationRequest create(Dafny.ISequence<char> KeyId) {
      return new EnableKeyRotationRequest(KeyId);
    }
    public bool is_EnableKeyRotationRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IEncryptionAlgorithmSpec {
    bool is_SYMMETRIC__DEFAULT { get; }
    bool is_RSAES__OAEP__SHA__1 { get; }
    bool is_RSAES__OAEP__SHA__256 { get; }
    _IEncryptionAlgorithmSpec DowncastClone();
  }
  public abstract class EncryptionAlgorithmSpec : _IEncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec() { }
    private static readonly _IEncryptionAlgorithmSpec theDefault = create_SYMMETRIC__DEFAULT();
    public static _IEncryptionAlgorithmSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>(ComAmazonawsKmsTypes_Compile.EncryptionAlgorithmSpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptionAlgorithmSpec create_SYMMETRIC__DEFAULT() {
      return new EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT();
    }
    public static _IEncryptionAlgorithmSpec create_RSAES__OAEP__SHA__1() {
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public static _IEncryptionAlgorithmSpec create_RSAES__OAEP__SHA__256() {
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public bool is_SYMMETRIC__DEFAULT { get { return this is EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT; } }
    public bool is_RSAES__OAEP__SHA__1 { get { return this is EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1; } }
    public bool is_RSAES__OAEP__SHA__256 { get { return this is EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256; } }
    public static System.Collections.Generic.IEnumerable<_IEncryptionAlgorithmSpec> AllSingletonConstructors {
      get {
        yield return EncryptionAlgorithmSpec.create_SYMMETRIC__DEFAULT();
        yield return EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1();
        yield return EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__256();
      }
    }
    public abstract _IEncryptionAlgorithmSpec DowncastClone();
  }
  public class EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT : EncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT() {
    }
    public override _IEncryptionAlgorithmSpec DowncastClone() {
      if (this is _IEncryptionAlgorithmSpec dt) { return dt; }
      return new EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT";
      return s;
    }
  }
  public class EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1 : EncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1() {
    }
    public override _IEncryptionAlgorithmSpec DowncastClone() {
      if (this is _IEncryptionAlgorithmSpec dt) { return dt; }
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1";
      return s;
    }
  }
  public class EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256 : EncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256() {
    }
    public override _IEncryptionAlgorithmSpec DowncastClone() {
      if (this is _IEncryptionAlgorithmSpec dt) { return dt; }
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256";
      return s;
    }
  }

  public interface _IEncryptRequest {
    bool is_EncryptRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_Plaintext { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IEncryptRequest DowncastClone();
  }
  public class EncryptRequest : _IEncryptRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<byte> Plaintext;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm;
    public EncryptRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Plaintext, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this.KeyId = KeyId;
      this.Plaintext = Plaintext;
      this.EncryptionContext = EncryptionContext;
      this.GrantTokens = GrantTokens;
      this.EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IEncryptRequest DowncastClone() {
      if (this is _IEncryptRequest dt) { return dt; }
      return new EncryptRequest(KeyId, Plaintext, EncryptionContext, GrantTokens, EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.EncryptRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Plaintext, oth.Plaintext) && object.Equals(this.EncryptionContext, oth.EncryptionContext) && object.Equals(this.GrantTokens, oth.GrantTokens) && object.Equals(this.EncryptionAlgorithm, oth.EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.EncryptRequest.EncryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _IEncryptRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default());
    public static _IEncryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptRequest>(ComAmazonawsKmsTypes_Compile.EncryptRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Plaintext, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new EncryptRequest(KeyId, Plaintext, EncryptionContext, GrantTokens, EncryptionAlgorithm);
    }
    public bool is_EncryptRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_Plaintext {
      get {
        return this.Plaintext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this.EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this.EncryptionAlgorithm;
      }
    }
  }

  public interface _IEncryptResponse {
    bool is_EncryptResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IEncryptResponse DowncastClone();
  }
  public class EncryptResponse : _IEncryptResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm;
    public EncryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this.CiphertextBlob = CiphertextBlob;
      this.KeyId = KeyId;
      this.EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IEncryptResponse DowncastClone() {
      if (this is _IEncryptResponse dt) { return dt; }
      return new EncryptResponse(CiphertextBlob, KeyId, EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.EncryptResponse;
      return oth != null && object.Equals(this.CiphertextBlob, oth.CiphertextBlob) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.EncryptionAlgorithm, oth.EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.EncryptResponse.EncryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _IEncryptResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default());
    public static _IEncryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptResponse>(ComAmazonawsKmsTypes_Compile.EncryptResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IEncryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new EncryptResponse(CiphertextBlob, KeyId, EncryptionAlgorithm);
    }
    public bool is_EncryptResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this.CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this.EncryptionAlgorithm;
      }
    }
  }

  public interface _IExpirationModelType {
    bool is_KEY__MATERIAL__EXPIRES { get; }
    bool is_KEY__MATERIAL__DOES__NOT__EXPIRE { get; }
    _IExpirationModelType DowncastClone();
  }
  public abstract class ExpirationModelType : _IExpirationModelType {
    public ExpirationModelType() { }
    private static readonly _IExpirationModelType theDefault = create_KEY__MATERIAL__EXPIRES();
    public static _IExpirationModelType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IExpirationModelType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IExpirationModelType>(ComAmazonawsKmsTypes_Compile.ExpirationModelType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IExpirationModelType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpirationModelType create_KEY__MATERIAL__EXPIRES() {
      return new ExpirationModelType_KEY__MATERIAL__EXPIRES();
    }
    public static _IExpirationModelType create_KEY__MATERIAL__DOES__NOT__EXPIRE() {
      return new ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE();
    }
    public bool is_KEY__MATERIAL__EXPIRES { get { return this is ExpirationModelType_KEY__MATERIAL__EXPIRES; } }
    public bool is_KEY__MATERIAL__DOES__NOT__EXPIRE { get { return this is ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE; } }
    public static System.Collections.Generic.IEnumerable<_IExpirationModelType> AllSingletonConstructors {
      get {
        yield return ExpirationModelType.create_KEY__MATERIAL__EXPIRES();
        yield return ExpirationModelType.create_KEY__MATERIAL__DOES__NOT__EXPIRE();
      }
    }
    public abstract _IExpirationModelType DowncastClone();
  }
  public class ExpirationModelType_KEY__MATERIAL__EXPIRES : ExpirationModelType {
    public ExpirationModelType_KEY__MATERIAL__EXPIRES() {
    }
    public override _IExpirationModelType DowncastClone() {
      if (this is _IExpirationModelType dt) { return dt; }
      return new ExpirationModelType_KEY__MATERIAL__EXPIRES();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ExpirationModelType_KEY__MATERIAL__EXPIRES;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ExpirationModelType.KEY_MATERIAL_EXPIRES";
      return s;
    }
  }
  public class ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE : ExpirationModelType {
    public ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE() {
    }
    public override _IExpirationModelType DowncastClone() {
      if (this is _IExpirationModelType dt) { return dt; }
      return new ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE";
      return s;
    }
  }

  public interface _IGenerateDataKeyPairRequest {
    bool is_GenerateDataKeyPairRequest { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec dtor_KeyPairSpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyPairRequest DowncastClone();
  }
  public class GenerateDataKeyPairRequest : _IGenerateDataKeyPairRequest {
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext;
    public readonly Dafny.ISequence<char> KeyId;
    public readonly ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec KeyPairSpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public GenerateDataKeyPairRequest(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.EncryptionContext = EncryptionContext;
      this.KeyId = KeyId;
      this.KeyPairSpec = KeyPairSpec;
      this.GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyPairRequest DowncastClone() {
      if (this is _IGenerateDataKeyPairRequest dt) { return dt; }
      return new GenerateDataKeyPairRequest(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairRequest;
      return oth != null && object.Equals(this.EncryptionContext, oth.EncryptionContext) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.KeyPairSpec, oth.KeyPairSpec) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyPairSpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairRequest.GenerateDataKeyPairRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyPairSpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyPairRequest theDefault = create(Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Dafny.Sequence<char>.Empty, ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IGenerateDataKeyPairRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairRequest>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairRequest create(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyPairRequest(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public bool is_GenerateDataKeyPairRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this.EncryptionContext;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec dtor_KeyPairSpec {
      get {
        return this.KeyPairSpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyPairResponse {
    bool is_GenerateDataKeyPairResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyPlaintext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> dtor_KeyPairSpec { get; }
    _IGenerateDataKeyPairResponse DowncastClone();
  }
  public class GenerateDataKeyPairResponse : _IGenerateDataKeyPairResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyPlaintext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> KeyPairSpec;
    public GenerateDataKeyPairResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyPlaintext, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> KeyPairSpec) {
      this.PrivateKeyCiphertextBlob = PrivateKeyCiphertextBlob;
      this.PrivateKeyPlaintext = PrivateKeyPlaintext;
      this.PublicKey = PublicKey;
      this.KeyId = KeyId;
      this.KeyPairSpec = KeyPairSpec;
    }
    public _IGenerateDataKeyPairResponse DowncastClone() {
      if (this is _IGenerateDataKeyPairResponse dt) { return dt; }
      return new GenerateDataKeyPairResponse(PrivateKeyCiphertextBlob, PrivateKeyPlaintext, PublicKey, KeyId, KeyPairSpec);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairResponse;
      return oth != null && object.Equals(this.PrivateKeyCiphertextBlob, oth.PrivateKeyCiphertextBlob) && object.Equals(this.PrivateKeyPlaintext, oth.PrivateKeyPlaintext) && object.Equals(this.PublicKey, oth.PublicKey) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.KeyPairSpec, oth.KeyPairSpec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PrivateKeyCiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PrivateKeyPlaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyPairSpec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairResponse.GenerateDataKeyPairResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.PrivateKeyCiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PrivateKeyPlaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyPairSpec);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyPairResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec>.Default());
    public static _IGenerateDataKeyPairResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairResponse>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyPlaintext, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> KeyPairSpec) {
      return new GenerateDataKeyPairResponse(PrivateKeyCiphertextBlob, PrivateKeyPlaintext, PublicKey, KeyId, KeyPairSpec);
    }
    public bool is_GenerateDataKeyPairResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob {
      get {
        return this.PrivateKeyCiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyPlaintext {
      get {
        return this.PrivateKeyPlaintext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this.PublicKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> dtor_KeyPairSpec {
      get {
        return this.KeyPairSpec;
      }
    }
  }

  public interface _IGenerateDataKeyPairWithoutPlaintextRequest {
    bool is_GenerateDataKeyPairWithoutPlaintextRequest { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec dtor_KeyPairSpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyPairWithoutPlaintextRequest DowncastClone();
  }
  public class GenerateDataKeyPairWithoutPlaintextRequest : _IGenerateDataKeyPairWithoutPlaintextRequest {
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext;
    public readonly Dafny.ISequence<char> KeyId;
    public readonly ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec KeyPairSpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public GenerateDataKeyPairWithoutPlaintextRequest(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.EncryptionContext = EncryptionContext;
      this.KeyId = KeyId;
      this.KeyPairSpec = KeyPairSpec;
      this.GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyPairWithoutPlaintextRequest DowncastClone() {
      if (this is _IGenerateDataKeyPairWithoutPlaintextRequest dt) { return dt; }
      return new GenerateDataKeyPairWithoutPlaintextRequest(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairWithoutPlaintextRequest;
      return oth != null && object.Equals(this.EncryptionContext, oth.EncryptionContext) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.KeyPairSpec, oth.KeyPairSpec) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyPairSpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairWithoutPlaintextRequest.GenerateDataKeyPairWithoutPlaintextRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyPairSpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyPairWithoutPlaintextRequest theDefault = create(Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Dafny.Sequence<char>.Empty, ComAmazonawsKmsTypes_Compile.DataKeyPairSpec.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IGenerateDataKeyPairWithoutPlaintextRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextRequest>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairWithoutPlaintextRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairWithoutPlaintextRequest create(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyPairWithoutPlaintextRequest(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public bool is_GenerateDataKeyPairWithoutPlaintextRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this.EncryptionContext;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec dtor_KeyPairSpec {
      get {
        return this.KeyPairSpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyPairWithoutPlaintextResponse {
    bool is_GenerateDataKeyPairWithoutPlaintextResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> dtor_KeyPairSpec { get; }
    _IGenerateDataKeyPairWithoutPlaintextResponse DowncastClone();
  }
  public class GenerateDataKeyPairWithoutPlaintextResponse : _IGenerateDataKeyPairWithoutPlaintextResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> KeyPairSpec;
    public GenerateDataKeyPairWithoutPlaintextResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> KeyPairSpec) {
      this.PrivateKeyCiphertextBlob = PrivateKeyCiphertextBlob;
      this.PublicKey = PublicKey;
      this.KeyId = KeyId;
      this.KeyPairSpec = KeyPairSpec;
    }
    public _IGenerateDataKeyPairWithoutPlaintextResponse DowncastClone() {
      if (this is _IGenerateDataKeyPairWithoutPlaintextResponse dt) { return dt; }
      return new GenerateDataKeyPairWithoutPlaintextResponse(PrivateKeyCiphertextBlob, PublicKey, KeyId, KeyPairSpec);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairWithoutPlaintextResponse;
      return oth != null && object.Equals(this.PrivateKeyCiphertextBlob, oth.PrivateKeyCiphertextBlob) && object.Equals(this.PublicKey, oth.PublicKey) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.KeyPairSpec, oth.KeyPairSpec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PrivateKeyCiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyPairSpec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairWithoutPlaintextResponse.GenerateDataKeyPairWithoutPlaintextResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.PrivateKeyCiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyPairSpec);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyPairWithoutPlaintextResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec>.Default());
    public static _IGenerateDataKeyPairWithoutPlaintextResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextResponse>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyPairWithoutPlaintextResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairWithoutPlaintextResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> KeyPairSpec) {
      return new GenerateDataKeyPairWithoutPlaintextResponse(PrivateKeyCiphertextBlob, PublicKey, KeyId, KeyPairSpec);
    }
    public bool is_GenerateDataKeyPairWithoutPlaintextResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob {
      get {
        return this.PrivateKeyCiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this.PublicKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeyPairSpec> dtor_KeyPairSpec {
      get {
        return this.KeyPairSpec;
      }
    }
  }

  public interface _IGenerateDataKeyRequest {
    bool is_GenerateDataKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<int> dtor_NumberOfBytes { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyRequest DowncastClone();
  }
  public class GenerateDataKeyRequest : _IGenerateDataKeyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext;
    public readonly Wrappers_Compile._IOption<int> NumberOfBytes;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> KeySpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public GenerateDataKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.KeyId = KeyId;
      this.EncryptionContext = EncryptionContext;
      this.NumberOfBytes = NumberOfBytes;
      this.KeySpec = KeySpec;
      this.GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyRequest DowncastClone() {
      if (this is _IGenerateDataKeyRequest dt) { return dt; }
      return new GenerateDataKeyRequest(KeyId, EncryptionContext, NumberOfBytes, KeySpec, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.EncryptionContext, oth.EncryptionContext) && object.Equals(this.NumberOfBytes, oth.NumberOfBytes) && object.Equals(this.KeySpec, oth.KeySpec) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NumberOfBytes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyRequest.GenerateDataKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NumberOfBytes);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IDataKeySpec>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IGenerateDataKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyRequest>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyRequest(KeyId, EncryptionContext, NumberOfBytes, KeySpec, GrantTokens);
    }
    public bool is_GenerateDataKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this.EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_NumberOfBytes {
      get {
        return this.NumberOfBytes;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> dtor_KeySpec {
      get {
        return this.KeySpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyResponse {
    bool is_GenerateDataKeyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    _IGenerateDataKeyResponse DowncastClone();
  }
  public class GenerateDataKeyResponse : _IGenerateDataKeyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public GenerateDataKeyResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      this.CiphertextBlob = CiphertextBlob;
      this.Plaintext = Plaintext;
      this.KeyId = KeyId;
    }
    public _IGenerateDataKeyResponse DowncastClone() {
      if (this is _IGenerateDataKeyResponse dt) { return dt; }
      return new GenerateDataKeyResponse(CiphertextBlob, Plaintext, KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyResponse;
      return oth != null && object.Equals(this.CiphertextBlob, oth.CiphertextBlob) && object.Equals(this.Plaintext, oth.Plaintext) && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyResponse.GenerateDataKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IGenerateDataKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyResponse>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return new GenerateDataKeyResponse(CiphertextBlob, Plaintext, KeyId);
    }
    public bool is_GenerateDataKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this.CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext {
      get {
        return this.Plaintext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IGenerateDataKeyWithoutPlaintextRequest {
    bool is_GenerateDataKeyWithoutPlaintextRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<int> dtor_NumberOfBytes { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyWithoutPlaintextRequest DowncastClone();
  }
  public class GenerateDataKeyWithoutPlaintextRequest : _IGenerateDataKeyWithoutPlaintextRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> KeySpec;
    public readonly Wrappers_Compile._IOption<int> NumberOfBytes;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public GenerateDataKeyWithoutPlaintextRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.KeyId = KeyId;
      this.EncryptionContext = EncryptionContext;
      this.KeySpec = KeySpec;
      this.NumberOfBytes = NumberOfBytes;
      this.GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyWithoutPlaintextRequest DowncastClone() {
      if (this is _IGenerateDataKeyWithoutPlaintextRequest dt) { return dt; }
      return new GenerateDataKeyWithoutPlaintextRequest(KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyWithoutPlaintextRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.EncryptionContext, oth.EncryptionContext) && object.Equals(this.KeySpec, oth.KeySpec) && object.Equals(this.NumberOfBytes, oth.NumberOfBytes) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NumberOfBytes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyWithoutPlaintextRequest.GenerateDataKeyWithoutPlaintextRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NumberOfBytes);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyWithoutPlaintextRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IDataKeySpec>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IGenerateDataKeyWithoutPlaintextRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextRequest>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyWithoutPlaintextRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyWithoutPlaintextRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyWithoutPlaintextRequest(KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens);
    }
    public bool is_GenerateDataKeyWithoutPlaintextRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this.EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IDataKeySpec> dtor_KeySpec {
      get {
        return this.KeySpec;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_NumberOfBytes {
      get {
        return this.NumberOfBytes;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyWithoutPlaintextResponse {
    bool is_GenerateDataKeyWithoutPlaintextResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    _IGenerateDataKeyWithoutPlaintextResponse DowncastClone();
  }
  public class GenerateDataKeyWithoutPlaintextResponse : _IGenerateDataKeyWithoutPlaintextResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public GenerateDataKeyWithoutPlaintextResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      this.CiphertextBlob = CiphertextBlob;
      this.KeyId = KeyId;
    }
    public _IGenerateDataKeyWithoutPlaintextResponse DowncastClone() {
      if (this is _IGenerateDataKeyWithoutPlaintextResponse dt) { return dt; }
      return new GenerateDataKeyWithoutPlaintextResponse(CiphertextBlob, KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateDataKeyWithoutPlaintextResponse;
      return oth != null && object.Equals(this.CiphertextBlob, oth.CiphertextBlob) && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateDataKeyWithoutPlaintextResponse.GenerateDataKeyWithoutPlaintextResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IGenerateDataKeyWithoutPlaintextResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IGenerateDataKeyWithoutPlaintextResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextResponse>(ComAmazonawsKmsTypes_Compile.GenerateDataKeyWithoutPlaintextResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyWithoutPlaintextResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return new GenerateDataKeyWithoutPlaintextResponse(CiphertextBlob, KeyId);
    }
    public bool is_GenerateDataKeyWithoutPlaintextResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this.CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IGenerateRandomRequest {
    bool is_GenerateRandomRequest { get; }
    Wrappers_Compile._IOption<int> dtor_NumberOfBytes { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    _IGenerateRandomRequest DowncastClone();
  }
  public class GenerateRandomRequest : _IGenerateRandomRequest {
    public readonly Wrappers_Compile._IOption<int> NumberOfBytes;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId;
    public GenerateRandomRequest(Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      this.NumberOfBytes = NumberOfBytes;
      this.CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IGenerateRandomRequest DowncastClone() {
      if (this is _IGenerateRandomRequest dt) { return dt; }
      return new GenerateRandomRequest(NumberOfBytes, CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateRandomRequest;
      return oth != null && object.Equals(this.NumberOfBytes, oth.NumberOfBytes) && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NumberOfBytes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateRandomRequest.GenerateRandomRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.NumberOfBytes);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly _IGenerateRandomRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IGenerateRandomRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateRandomRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateRandomRequest>(ComAmazonawsKmsTypes_Compile.GenerateRandomRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateRandomRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRandomRequest create(Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      return new GenerateRandomRequest(NumberOfBytes, CustomKeyStoreId);
    }
    public bool is_GenerateRandomRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_NumberOfBytes {
      get {
        return this.NumberOfBytes;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
  }

  public interface _IGenerateRandomResponse {
    bool is_GenerateRandomResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext { get; }
    _IGenerateRandomResponse DowncastClone();
  }
  public class GenerateRandomResponse : _IGenerateRandomResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext;
    public GenerateRandomResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext) {
      this.Plaintext = Plaintext;
    }
    public _IGenerateRandomResponse DowncastClone() {
      if (this is _IGenerateRandomResponse dt) { return dt; }
      return new GenerateRandomResponse(Plaintext);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GenerateRandomResponse;
      return oth != null && object.Equals(this.Plaintext, oth.Plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Plaintext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GenerateRandomResponse.GenerateRandomResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.Plaintext);
      s += ")";
      return s;
    }
    private static readonly _IGenerateRandomResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static _IGenerateRandomResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateRandomResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateRandomResponse>(ComAmazonawsKmsTypes_Compile.GenerateRandomResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGenerateRandomResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRandomResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext) {
      return new GenerateRandomResponse(Plaintext);
    }
    public bool is_GenerateRandomResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext {
      get {
        return this.Plaintext;
      }
    }
  }

  public interface _IGetKeyPolicyRequest {
    bool is_GetKeyPolicyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_PolicyName { get; }
    _IGetKeyPolicyRequest DowncastClone();
  }
  public class GetKeyPolicyRequest : _IGetKeyPolicyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<char> PolicyName;
    public GetKeyPolicyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName) {
      this.KeyId = KeyId;
      this.PolicyName = PolicyName;
    }
    public _IGetKeyPolicyRequest DowncastClone() {
      if (this is _IGetKeyPolicyRequest dt) { return dt; }
      return new GetKeyPolicyRequest(KeyId, PolicyName);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetKeyPolicyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.PolicyName, oth.PolicyName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PolicyName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetKeyPolicyRequest.GetKeyPolicyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PolicyName);
      s += ")";
      return s;
    }
    private static readonly _IGetKeyPolicyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _IGetKeyPolicyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyPolicyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyPolicyRequest>(ComAmazonawsKmsTypes_Compile.GetKeyPolicyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyPolicyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyPolicyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName) {
      return new GetKeyPolicyRequest(KeyId, PolicyName);
    }
    public bool is_GetKeyPolicyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_PolicyName {
      get {
        return this.PolicyName;
      }
    }
  }

  public interface _IGetKeyPolicyResponse {
    bool is_GetKeyPolicyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy { get; }
    _IGetKeyPolicyResponse DowncastClone();
  }
  public class GetKeyPolicyResponse : _IGetKeyPolicyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy;
    public GetKeyPolicyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy) {
      this.Policy = Policy;
    }
    public _IGetKeyPolicyResponse DowncastClone() {
      if (this is _IGetKeyPolicyResponse dt) { return dt; }
      return new GetKeyPolicyResponse(Policy);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetKeyPolicyResponse;
      return oth != null && object.Equals(this.Policy, oth.Policy);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Policy));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetKeyPolicyResponse.GetKeyPolicyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.Policy);
      s += ")";
      return s;
    }
    private static readonly _IGetKeyPolicyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IGetKeyPolicyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyPolicyResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyPolicyResponse>(ComAmazonawsKmsTypes_Compile.GetKeyPolicyResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyPolicyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyPolicyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy) {
      return new GetKeyPolicyResponse(Policy);
    }
    public bool is_GetKeyPolicyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy {
      get {
        return this.Policy;
      }
    }
  }

  public interface _IGetKeyRotationStatusRequest {
    bool is_GetKeyRotationStatusRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IGetKeyRotationStatusRequest DowncastClone();
  }
  public class GetKeyRotationStatusRequest : _IGetKeyRotationStatusRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public GetKeyRotationStatusRequest(Dafny.ISequence<char> KeyId) {
      this.KeyId = KeyId;
    }
    public _IGetKeyRotationStatusRequest DowncastClone() {
      if (this is _IGetKeyRotationStatusRequest dt) { return dt; }
      return new GetKeyRotationStatusRequest(KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetKeyRotationStatusRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetKeyRotationStatusRequest.GetKeyRotationStatusRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ")";
      return s;
    }
    private static readonly _IGetKeyRotationStatusRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static _IGetKeyRotationStatusRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusRequest>(ComAmazonawsKmsTypes_Compile.GetKeyRotationStatusRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyRotationStatusRequest create(Dafny.ISequence<char> KeyId) {
      return new GetKeyRotationStatusRequest(KeyId);
    }
    public bool is_GetKeyRotationStatusRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
  }

  public interface _IGetKeyRotationStatusResponse {
    bool is_GetKeyRotationStatusResponse { get; }
    Wrappers_Compile._IOption<bool> dtor_KeyRotationEnabled { get; }
    _IGetKeyRotationStatusResponse DowncastClone();
  }
  public class GetKeyRotationStatusResponse : _IGetKeyRotationStatusResponse {
    public readonly Wrappers_Compile._IOption<bool> KeyRotationEnabled;
    public GetKeyRotationStatusResponse(Wrappers_Compile._IOption<bool> KeyRotationEnabled) {
      this.KeyRotationEnabled = KeyRotationEnabled;
    }
    public _IGetKeyRotationStatusResponse DowncastClone() {
      if (this is _IGetKeyRotationStatusResponse dt) { return dt; }
      return new GetKeyRotationStatusResponse(KeyRotationEnabled);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetKeyRotationStatusResponse;
      return oth != null && object.Equals(this.KeyRotationEnabled, oth.KeyRotationEnabled);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyRotationEnabled));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetKeyRotationStatusResponse.GetKeyRotationStatusResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyRotationEnabled);
      s += ")";
      return s;
    }
    private static readonly _IGetKeyRotationStatusResponse theDefault = create(Wrappers_Compile.Option<bool>.Default());
    public static _IGetKeyRotationStatusResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusResponse>(ComAmazonawsKmsTypes_Compile.GetKeyRotationStatusResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyRotationStatusResponse create(Wrappers_Compile._IOption<bool> KeyRotationEnabled) {
      return new GetKeyRotationStatusResponse(KeyRotationEnabled);
    }
    public bool is_GetKeyRotationStatusResponse { get { return true; } }
    public Wrappers_Compile._IOption<bool> dtor_KeyRotationEnabled {
      get {
        return this.KeyRotationEnabled;
      }
    }
  }

  public interface _IGetParametersForImportRequest {
    bool is_GetParametersForImportRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    ComAmazonawsKmsTypes_Compile._IAlgorithmSpec dtor_WrappingAlgorithm { get; }
    ComAmazonawsKmsTypes_Compile._IWrappingKeySpec dtor_WrappingKeySpec { get; }
    _IGetParametersForImportRequest DowncastClone();
  }
  public class GetParametersForImportRequest : _IGetParametersForImportRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly ComAmazonawsKmsTypes_Compile._IAlgorithmSpec WrappingAlgorithm;
    public readonly ComAmazonawsKmsTypes_Compile._IWrappingKeySpec WrappingKeySpec;
    public GetParametersForImportRequest(Dafny.ISequence<char> KeyId, ComAmazonawsKmsTypes_Compile._IAlgorithmSpec WrappingAlgorithm, ComAmazonawsKmsTypes_Compile._IWrappingKeySpec WrappingKeySpec) {
      this.KeyId = KeyId;
      this.WrappingAlgorithm = WrappingAlgorithm;
      this.WrappingKeySpec = WrappingKeySpec;
    }
    public _IGetParametersForImportRequest DowncastClone() {
      if (this is _IGetParametersForImportRequest dt) { return dt; }
      return new GetParametersForImportRequest(KeyId, WrappingAlgorithm, WrappingKeySpec);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetParametersForImportRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.WrappingAlgorithm, oth.WrappingAlgorithm) && object.Equals(this.WrappingKeySpec, oth.WrappingKeySpec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.WrappingAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.WrappingKeySpec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetParametersForImportRequest.GetParametersForImportRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.WrappingAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.WrappingKeySpec);
      s += ")";
      return s;
    }
    private static readonly _IGetParametersForImportRequest theDefault = create(Dafny.Sequence<char>.Empty, ComAmazonawsKmsTypes_Compile.AlgorithmSpec.Default(), ComAmazonawsKmsTypes_Compile.WrappingKeySpec.Default());
    public static _IGetParametersForImportRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetParametersForImportRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetParametersForImportRequest>(ComAmazonawsKmsTypes_Compile.GetParametersForImportRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetParametersForImportRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetParametersForImportRequest create(Dafny.ISequence<char> KeyId, ComAmazonawsKmsTypes_Compile._IAlgorithmSpec WrappingAlgorithm, ComAmazonawsKmsTypes_Compile._IWrappingKeySpec WrappingKeySpec) {
      return new GetParametersForImportRequest(KeyId, WrappingAlgorithm, WrappingKeySpec);
    }
    public bool is_GetParametersForImportRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public ComAmazonawsKmsTypes_Compile._IAlgorithmSpec dtor_WrappingAlgorithm {
      get {
        return this.WrappingAlgorithm;
      }
    }
    public ComAmazonawsKmsTypes_Compile._IWrappingKeySpec dtor_WrappingKeySpec {
      get {
        return this.WrappingKeySpec;
      }
    }
  }

  public interface _IGetParametersForImportResponse {
    bool is_GetParametersForImportResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_ImportToken { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ParametersValidTo { get; }
    _IGetParametersForImportResponse DowncastClone();
  }
  public class GetParametersForImportResponse : _IGetParametersForImportResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> ImportToken;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> ParametersValidTo;
    public GetParametersForImportResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> ImportToken, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> ParametersValidTo) {
      this.KeyId = KeyId;
      this.ImportToken = ImportToken;
      this.PublicKey = PublicKey;
      this.ParametersValidTo = ParametersValidTo;
    }
    public _IGetParametersForImportResponse DowncastClone() {
      if (this is _IGetParametersForImportResponse dt) { return dt; }
      return new GetParametersForImportResponse(KeyId, ImportToken, PublicKey, ParametersValidTo);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetParametersForImportResponse;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.ImportToken, oth.ImportToken) && object.Equals(this.PublicKey, oth.PublicKey) && object.Equals(this.ParametersValidTo, oth.ParametersValidTo);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ImportToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ParametersValidTo));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetParametersForImportResponse.GetParametersForImportResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ImportToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ParametersValidTo);
      s += ")";
      return s;
    }
    private static readonly _IGetParametersForImportResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IGetParametersForImportResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetParametersForImportResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetParametersForImportResponse>(ComAmazonawsKmsTypes_Compile.GetParametersForImportResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetParametersForImportResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetParametersForImportResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> ImportToken, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> ParametersValidTo) {
      return new GetParametersForImportResponse(KeyId, ImportToken, PublicKey, ParametersValidTo);
    }
    public bool is_GetParametersForImportResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_ImportToken {
      get {
        return this.ImportToken;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this.PublicKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ParametersValidTo {
      get {
        return this.ParametersValidTo;
      }
    }
  }

  public interface _IGetPublicKeyRequest {
    bool is_GetPublicKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGetPublicKeyRequest DowncastClone();
  }
  public class GetPublicKeyRequest : _IGetPublicKeyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public GetPublicKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.KeyId = KeyId;
      this.GrantTokens = GrantTokens;
    }
    public _IGetPublicKeyRequest DowncastClone() {
      if (this is _IGetPublicKeyRequest dt) { return dt; }
      return new GetPublicKeyRequest(KeyId, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetPublicKeyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetPublicKeyRequest.GetPublicKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IGetPublicKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IGetPublicKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetPublicKeyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetPublicKeyRequest>(ComAmazonawsKmsTypes_Compile.GetPublicKeyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetPublicKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetPublicKeyRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GetPublicKeyRequest(KeyId, GrantTokens);
    }
    public bool is_GetPublicKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IGetPublicKeyResponse {
    bool is_GetPublicKeyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> dtor_KeyUsage { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> dtor_SigningAlgorithms { get; }
    _IGetPublicKeyResponse DowncastClone();
  }
  public class GetPublicKeyResponse : _IGetPublicKeyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> EncryptionAlgorithms;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> SigningAlgorithms;
    public GetPublicKeyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> SigningAlgorithms) {
      this.KeyId = KeyId;
      this.PublicKey = PublicKey;
      this.CustomerMasterKeySpec = CustomerMasterKeySpec;
      this.KeySpec = KeySpec;
      this.KeyUsage = KeyUsage;
      this.EncryptionAlgorithms = EncryptionAlgorithms;
      this.SigningAlgorithms = SigningAlgorithms;
    }
    public _IGetPublicKeyResponse DowncastClone() {
      if (this is _IGetPublicKeyResponse dt) { return dt; }
      return new GetPublicKeyResponse(KeyId, PublicKey, CustomerMasterKeySpec, KeySpec, KeyUsage, EncryptionAlgorithms, SigningAlgorithms);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GetPublicKeyResponse;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.PublicKey, oth.PublicKey) && object.Equals(this.CustomerMasterKeySpec, oth.CustomerMasterKeySpec) && object.Equals(this.KeySpec, oth.KeySpec) && object.Equals(this.KeyUsage, oth.KeyUsage) && object.Equals(this.EncryptionAlgorithms, oth.EncryptionAlgorithms) && object.Equals(this.SigningAlgorithms, oth.SigningAlgorithms);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomerMasterKeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyUsage));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionAlgorithms));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SigningAlgorithms));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GetPublicKeyResponse.GetPublicKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomerMasterKeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyUsage);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionAlgorithms);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SigningAlgorithms);
      s += ")";
      return s;
    }
    private static readonly _IGetPublicKeyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeySpec>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyUsageType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>>.Default());
    public static _IGetPublicKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetPublicKeyResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetPublicKeyResponse>(ComAmazonawsKmsTypes_Compile.GetPublicKeyResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGetPublicKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetPublicKeyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> SigningAlgorithms) {
      return new GetPublicKeyResponse(KeyId, PublicKey, CustomerMasterKeySpec, KeySpec, KeyUsage, EncryptionAlgorithms, SigningAlgorithms);
    }
    public bool is_GetPublicKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this.PublicKey;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec {
      get {
        return this.CustomerMasterKeySpec;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> dtor_KeySpec {
      get {
        return this.KeySpec;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> dtor_KeyUsage {
      get {
        return this.KeyUsage;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms {
      get {
        return this.EncryptionAlgorithms;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> dtor_SigningAlgorithms {
      get {
        return this.SigningAlgorithms;
      }
    }
  }

  public interface _IGrantConstraints {
    bool is_GrantConstraints { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextSubset { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextEquals { get; }
    _IGrantConstraints DowncastClone();
  }
  public class GrantConstraints : _IGrantConstraints {
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextSubset;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextEquals;
    public GrantConstraints(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextSubset, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextEquals) {
      this.EncryptionContextSubset = EncryptionContextSubset;
      this.EncryptionContextEquals = EncryptionContextEquals;
    }
    public _IGrantConstraints DowncastClone() {
      if (this is _IGrantConstraints dt) { return dt; }
      return new GrantConstraints(EncryptionContextSubset, EncryptionContextEquals);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantConstraints;
      return oth != null && object.Equals(this.EncryptionContextSubset, oth.EncryptionContextSubset) && object.Equals(this.EncryptionContextEquals, oth.EncryptionContextEquals);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContextSubset));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionContextEquals));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantConstraints.GrantConstraints";
      s += "(";
      s += Dafny.Helpers.ToString(this.EncryptionContextSubset);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionContextEquals);
      s += ")";
      return s;
    }
    private static readonly _IGrantConstraints theDefault = create(Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default());
    public static _IGrantConstraints Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantConstraints> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantConstraints>(ComAmazonawsKmsTypes_Compile.GrantConstraints.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantConstraints> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGrantConstraints create(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextSubset, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextEquals) {
      return new GrantConstraints(EncryptionContextSubset, EncryptionContextEquals);
    }
    public bool is_GrantConstraints { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextSubset {
      get {
        return this.EncryptionContextSubset;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextEquals {
      get {
        return this.EncryptionContextEquals;
      }
    }
  }

  public partial class GrantIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IGrantListEntry {
    bool is_GrantListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_IssuingAccount { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation>> dtor_Operations { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> dtor_Constraints { get; }
    _IGrantListEntry DowncastClone();
  }
  public class GrantListEntry : _IGrantListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Name;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> IssuingAccount;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation>> Operations;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> Constraints;
    public GrantListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> IssuingAccount, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation>> Operations, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> Constraints) {
      this.KeyId = KeyId;
      this.GrantId = GrantId;
      this.Name = Name;
      this.CreationDate = CreationDate;
      this.GranteePrincipal = GranteePrincipal;
      this.RetiringPrincipal = RetiringPrincipal;
      this.IssuingAccount = IssuingAccount;
      this.Operations = Operations;
      this.Constraints = Constraints;
    }
    public _IGrantListEntry DowncastClone() {
      if (this is _IGrantListEntry dt) { return dt; }
      return new GrantListEntry(KeyId, GrantId, Name, CreationDate, GranteePrincipal, RetiringPrincipal, IssuingAccount, Operations, Constraints);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantListEntry;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.GrantId, oth.GrantId) && object.Equals(this.Name, oth.Name) && object.Equals(this.CreationDate, oth.CreationDate) && object.Equals(this.GranteePrincipal, oth.GranteePrincipal) && object.Equals(this.RetiringPrincipal, oth.RetiringPrincipal) && object.Equals(this.IssuingAccount, oth.IssuingAccount) && object.Equals(this.Operations, oth.Operations) && object.Equals(this.Constraints, oth.Constraints);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CreationDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GranteePrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.RetiringPrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.IssuingAccount));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Operations));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Constraints));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantListEntry.GrantListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Name);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CreationDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GranteePrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this.RetiringPrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this.IssuingAccount);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Operations);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Constraints);
      s += ")";
      return s;
    }
    private static readonly _IGrantListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IGrantConstraints>.Default());
    public static _IGrantListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantListEntry> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantListEntry>(ComAmazonawsKmsTypes_Compile.GrantListEntry.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGrantListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> IssuingAccount, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation>> Operations, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> Constraints) {
      return new GrantListEntry(KeyId, GrantId, Name, CreationDate, GranteePrincipal, RetiringPrincipal, IssuingAccount, Operations, Constraints);
    }
    public bool is_GrantListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this.GrantId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name {
      get {
        return this.Name;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this.CreationDate;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal {
      get {
        return this.GranteePrincipal;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal {
      get {
        return this.RetiringPrincipal;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_IssuingAccount {
      get {
        return this.IssuingAccount;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantOperation>> dtor_Operations {
      get {
        return this.Operations;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IGrantConstraints> dtor_Constraints {
      get {
        return this.Constraints;
      }
    }
  }

  public partial class GrantNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IGrantOperation {
    bool is_Decrypt { get; }
    bool is_Encrypt { get; }
    bool is_GenerateDataKey { get; }
    bool is_GenerateDataKeyWithoutPlaintext { get; }
    bool is_ReEncryptFrom { get; }
    bool is_ReEncryptTo { get; }
    bool is_Sign { get; }
    bool is_Verify { get; }
    bool is_GetPublicKey { get; }
    bool is_CreateGrant { get; }
    bool is_RetireGrant { get; }
    bool is_DescribeKey { get; }
    bool is_GenerateDataKeyPair { get; }
    bool is_GenerateDataKeyPairWithoutPlaintext { get; }
    _IGrantOperation DowncastClone();
  }
  public abstract class GrantOperation : _IGrantOperation {
    public GrantOperation() { }
    private static readonly _IGrantOperation theDefault = create_Decrypt();
    public static _IGrantOperation Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantOperation> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantOperation>(ComAmazonawsKmsTypes_Compile.GrantOperation.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IGrantOperation> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGrantOperation create_Decrypt() {
      return new GrantOperation_Decrypt();
    }
    public static _IGrantOperation create_Encrypt() {
      return new GrantOperation_Encrypt();
    }
    public static _IGrantOperation create_GenerateDataKey() {
      return new GrantOperation_GenerateDataKey();
    }
    public static _IGrantOperation create_GenerateDataKeyWithoutPlaintext() {
      return new GrantOperation_GenerateDataKeyWithoutPlaintext();
    }
    public static _IGrantOperation create_ReEncryptFrom() {
      return new GrantOperation_ReEncryptFrom();
    }
    public static _IGrantOperation create_ReEncryptTo() {
      return new GrantOperation_ReEncryptTo();
    }
    public static _IGrantOperation create_Sign() {
      return new GrantOperation_Sign();
    }
    public static _IGrantOperation create_Verify() {
      return new GrantOperation_Verify();
    }
    public static _IGrantOperation create_GetPublicKey() {
      return new GrantOperation_GetPublicKey();
    }
    public static _IGrantOperation create_CreateGrant() {
      return new GrantOperation_CreateGrant();
    }
    public static _IGrantOperation create_RetireGrant() {
      return new GrantOperation_RetireGrant();
    }
    public static _IGrantOperation create_DescribeKey() {
      return new GrantOperation_DescribeKey();
    }
    public static _IGrantOperation create_GenerateDataKeyPair() {
      return new GrantOperation_GenerateDataKeyPair();
    }
    public static _IGrantOperation create_GenerateDataKeyPairWithoutPlaintext() {
      return new GrantOperation_GenerateDataKeyPairWithoutPlaintext();
    }
    public bool is_Decrypt { get { return this is GrantOperation_Decrypt; } }
    public bool is_Encrypt { get { return this is GrantOperation_Encrypt; } }
    public bool is_GenerateDataKey { get { return this is GrantOperation_GenerateDataKey; } }
    public bool is_GenerateDataKeyWithoutPlaintext { get { return this is GrantOperation_GenerateDataKeyWithoutPlaintext; } }
    public bool is_ReEncryptFrom { get { return this is GrantOperation_ReEncryptFrom; } }
    public bool is_ReEncryptTo { get { return this is GrantOperation_ReEncryptTo; } }
    public bool is_Sign { get { return this is GrantOperation_Sign; } }
    public bool is_Verify { get { return this is GrantOperation_Verify; } }
    public bool is_GetPublicKey { get { return this is GrantOperation_GetPublicKey; } }
    public bool is_CreateGrant { get { return this is GrantOperation_CreateGrant; } }
    public bool is_RetireGrant { get { return this is GrantOperation_RetireGrant; } }
    public bool is_DescribeKey { get { return this is GrantOperation_DescribeKey; } }
    public bool is_GenerateDataKeyPair { get { return this is GrantOperation_GenerateDataKeyPair; } }
    public bool is_GenerateDataKeyPairWithoutPlaintext { get { return this is GrantOperation_GenerateDataKeyPairWithoutPlaintext; } }
    public static System.Collections.Generic.IEnumerable<_IGrantOperation> AllSingletonConstructors {
      get {
        yield return GrantOperation.create_Decrypt();
        yield return GrantOperation.create_Encrypt();
        yield return GrantOperation.create_GenerateDataKey();
        yield return GrantOperation.create_GenerateDataKeyWithoutPlaintext();
        yield return GrantOperation.create_ReEncryptFrom();
        yield return GrantOperation.create_ReEncryptTo();
        yield return GrantOperation.create_Sign();
        yield return GrantOperation.create_Verify();
        yield return GrantOperation.create_GetPublicKey();
        yield return GrantOperation.create_CreateGrant();
        yield return GrantOperation.create_RetireGrant();
        yield return GrantOperation.create_DescribeKey();
        yield return GrantOperation.create_GenerateDataKeyPair();
        yield return GrantOperation.create_GenerateDataKeyPairWithoutPlaintext();
      }
    }
    public abstract _IGrantOperation DowncastClone();
  }
  public class GrantOperation_Decrypt : GrantOperation {
    public GrantOperation_Decrypt() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Decrypt();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_Decrypt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.Decrypt";
      return s;
    }
  }
  public class GrantOperation_Encrypt : GrantOperation {
    public GrantOperation_Encrypt() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Encrypt();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_Encrypt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.Encrypt";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKey : GrantOperation {
    public GrantOperation_GenerateDataKey() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKey();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_GenerateDataKey;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.GenerateDataKey";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKeyWithoutPlaintext : GrantOperation {
    public GrantOperation_GenerateDataKeyWithoutPlaintext() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKeyWithoutPlaintext();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_GenerateDataKeyWithoutPlaintext;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.GenerateDataKeyWithoutPlaintext";
      return s;
    }
  }
  public class GrantOperation_ReEncryptFrom : GrantOperation {
    public GrantOperation_ReEncryptFrom() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_ReEncryptFrom();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_ReEncryptFrom;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.ReEncryptFrom";
      return s;
    }
  }
  public class GrantOperation_ReEncryptTo : GrantOperation {
    public GrantOperation_ReEncryptTo() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_ReEncryptTo();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_ReEncryptTo;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.ReEncryptTo";
      return s;
    }
  }
  public class GrantOperation_Sign : GrantOperation {
    public GrantOperation_Sign() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Sign();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_Sign;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.Sign";
      return s;
    }
  }
  public class GrantOperation_Verify : GrantOperation {
    public GrantOperation_Verify() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Verify();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_Verify;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.Verify";
      return s;
    }
  }
  public class GrantOperation_GetPublicKey : GrantOperation {
    public GrantOperation_GetPublicKey() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GetPublicKey();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_GetPublicKey;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.GetPublicKey";
      return s;
    }
  }
  public class GrantOperation_CreateGrant : GrantOperation {
    public GrantOperation_CreateGrant() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_CreateGrant();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_CreateGrant;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.CreateGrant";
      return s;
    }
  }
  public class GrantOperation_RetireGrant : GrantOperation {
    public GrantOperation_RetireGrant() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_RetireGrant();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_RetireGrant;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.RetireGrant";
      return s;
    }
  }
  public class GrantOperation_DescribeKey : GrantOperation {
    public GrantOperation_DescribeKey() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_DescribeKey();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_DescribeKey;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.DescribeKey";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKeyPair : GrantOperation {
    public GrantOperation_GenerateDataKeyPair() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKeyPair();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_GenerateDataKeyPair;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.GenerateDataKeyPair";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKeyPairWithoutPlaintext : GrantOperation {
    public GrantOperation_GenerateDataKeyPairWithoutPlaintext() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKeyPairWithoutPlaintext();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.GrantOperation_GenerateDataKeyPairWithoutPlaintext;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.GrantOperation.GenerateDataKeyPairWithoutPlaintext";
      return s;
    }
  }

  public partial class GrantTokenList {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>>(Dafny.Sequence<Dafny.ISequence<char>>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class GrantTokenType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IImportKeyMaterialRequest {
    bool is_ImportKeyMaterialRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_ImportToken { get; }
    Dafny.ISequence<byte> dtor_EncryptedKeyMaterial { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> dtor_ExpirationModel { get; }
    _IImportKeyMaterialRequest DowncastClone();
  }
  public class ImportKeyMaterialRequest : _IImportKeyMaterialRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<byte> ImportToken;
    public readonly Dafny.ISequence<byte> EncryptedKeyMaterial;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> ExpirationModel;
    public ImportKeyMaterialRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> ImportToken, Dafny.ISequence<byte> EncryptedKeyMaterial, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> ExpirationModel) {
      this.KeyId = KeyId;
      this.ImportToken = ImportToken;
      this.EncryptedKeyMaterial = EncryptedKeyMaterial;
      this.ValidTo = ValidTo;
      this.ExpirationModel = ExpirationModel;
    }
    public _IImportKeyMaterialRequest DowncastClone() {
      if (this is _IImportKeyMaterialRequest dt) { return dt; }
      return new ImportKeyMaterialRequest(KeyId, ImportToken, EncryptedKeyMaterial, ValidTo, ExpirationModel);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ImportKeyMaterialRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.ImportToken, oth.ImportToken) && object.Equals(this.EncryptedKeyMaterial, oth.EncryptedKeyMaterial) && object.Equals(this.ValidTo, oth.ValidTo) && object.Equals(this.ExpirationModel, oth.ExpirationModel);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ImportToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptedKeyMaterial));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ValidTo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ExpirationModel));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ImportKeyMaterialRequest.ImportKeyMaterialRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ImportToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptedKeyMaterial);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ValidTo);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ExpirationModel);
      s += ")";
      return s;
    }
    private static readonly _IImportKeyMaterialRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IExpirationModelType>.Default());
    public static _IImportKeyMaterialRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IImportKeyMaterialRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IImportKeyMaterialRequest>(ComAmazonawsKmsTypes_Compile.ImportKeyMaterialRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IImportKeyMaterialRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImportKeyMaterialRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> ImportToken, Dafny.ISequence<byte> EncryptedKeyMaterial, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> ExpirationModel) {
      return new ImportKeyMaterialRequest(KeyId, ImportToken, EncryptedKeyMaterial, ValidTo, ExpirationModel);
    }
    public bool is_ImportKeyMaterialRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_ImportToken {
      get {
        return this.ImportToken;
      }
    }
    public Dafny.ISequence<byte> dtor_EncryptedKeyMaterial {
      get {
        return this.EncryptedKeyMaterial;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo {
      get {
        return this.ValidTo;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> dtor_ExpirationModel {
      get {
        return this.ExpirationModel;
      }
    }
  }

  public interface _IImportKeyMaterialResponse {
    bool is_ImportKeyMaterialResponse { get; }
    _IImportKeyMaterialResponse DowncastClone();
  }
  public class ImportKeyMaterialResponse : _IImportKeyMaterialResponse {
    public ImportKeyMaterialResponse() {
    }
    public _IImportKeyMaterialResponse DowncastClone() {
      if (this is _IImportKeyMaterialResponse dt) { return dt; }
      return new ImportKeyMaterialResponse();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ImportKeyMaterialResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ImportKeyMaterialResponse.ImportKeyMaterialResponse";
      return s;
    }
    private static readonly _IImportKeyMaterialResponse theDefault = create();
    public static _IImportKeyMaterialResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IImportKeyMaterialResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IImportKeyMaterialResponse>(ComAmazonawsKmsTypes_Compile.ImportKeyMaterialResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IImportKeyMaterialResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImportKeyMaterialResponse create() {
      return new ImportKeyMaterialResponse();
    }
    public bool is_ImportKeyMaterialResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IImportKeyMaterialResponse> AllSingletonConstructors {
      get {
        yield return ImportKeyMaterialResponse.create();
      }
    }
  }

  public partial class KeyIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IKeyListEntry {
    bool is_KeyListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyArn { get; }
    _IKeyListEntry DowncastClone();
  }
  public class KeyListEntry : _IKeyListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyArn;
    public KeyListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyArn) {
      this.KeyId = KeyId;
      this.KeyArn = KeyArn;
    }
    public _IKeyListEntry DowncastClone() {
      if (this is _IKeyListEntry dt) { return dt; }
      return new KeyListEntry(KeyId, KeyArn);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyListEntry;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.KeyArn, oth.KeyArn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyArn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyListEntry.KeyListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyArn);
      s += ")";
      return s;
    }
    private static readonly _IKeyListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IKeyListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyListEntry> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyListEntry>(ComAmazonawsKmsTypes_Compile.KeyListEntry.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyArn) {
      return new KeyListEntry(KeyId, KeyArn);
    }
    public bool is_KeyListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyArn {
      get {
        return this.KeyArn;
      }
    }
  }

  public interface IKeyManagementServiceClient {
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionResponse, ComAmazonawsKmsTypes_Compile._IError> CancelKeyDeletion(ComAmazonawsKmsTypes_Compile._ICancelKeyDeletionRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreResponse, ComAmazonawsKmsTypes_Compile._IError> ConnectCustomKeyStore(ComAmazonawsKmsTypes_Compile._IConnectCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> CreateAlias(ComAmazonawsKmsTypes_Compile._ICreateAliasRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreResponse, ComAmazonawsKmsTypes_Compile._IError> CreateCustomKeyStore(ComAmazonawsKmsTypes_Compile._ICreateCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._ICreateGrantResponse, ComAmazonawsKmsTypes_Compile._IError> CreateGrant(ComAmazonawsKmsTypes_Compile._ICreateGrantRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._ICreateKeyResponse, ComAmazonawsKmsTypes_Compile._IError> CreateKey(ComAmazonawsKmsTypes_Compile._ICreateKeyRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IDecryptResponse, ComAmazonawsKmsTypes_Compile._IError> Decrypt(ComAmazonawsKmsTypes_Compile._IDecryptRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> DeleteAlias(ComAmazonawsKmsTypes_Compile._IDeleteAliasRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreResponse, ComAmazonawsKmsTypes_Compile._IError> DeleteCustomKeyStore(ComAmazonawsKmsTypes_Compile._IDeleteCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> DeleteImportedKeyMaterial(ComAmazonawsKmsTypes_Compile._IDeleteImportedKeyMaterialRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresResponse, ComAmazonawsKmsTypes_Compile._IError> DescribeCustomKeyStores(ComAmazonawsKmsTypes_Compile._IDescribeCustomKeyStoresRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IDescribeKeyResponse, ComAmazonawsKmsTypes_Compile._IError> DescribeKey(ComAmazonawsKmsTypes_Compile._IDescribeKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> DisableKey(ComAmazonawsKmsTypes_Compile._IDisableKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> DisableKeyRotation(ComAmazonawsKmsTypes_Compile._IDisableKeyRotationRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreResponse, ComAmazonawsKmsTypes_Compile._IError> DisconnectCustomKeyStore(ComAmazonawsKmsTypes_Compile._IDisconnectCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> EnableKey(ComAmazonawsKmsTypes_Compile._IEnableKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> EnableKeyRotation(ComAmazonawsKmsTypes_Compile._IEnableKeyRotationRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IEncryptResponse, ComAmazonawsKmsTypes_Compile._IError> Encrypt(ComAmazonawsKmsTypes_Compile._IEncryptRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyResponse, ComAmazonawsKmsTypes_Compile._IError> GenerateDataKey(ComAmazonawsKmsTypes_Compile._IGenerateDataKeyRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairResponse, ComAmazonawsKmsTypes_Compile._IError> GenerateDataKeyPair(ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextResponse, ComAmazonawsKmsTypes_Compile._IError> GenerateDataKeyPairWithoutPlaintext(ComAmazonawsKmsTypes_Compile._IGenerateDataKeyPairWithoutPlaintextRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextResponse, ComAmazonawsKmsTypes_Compile._IError> GenerateDataKeyWithoutPlaintext(ComAmazonawsKmsTypes_Compile._IGenerateDataKeyWithoutPlaintextRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGenerateRandomResponse, ComAmazonawsKmsTypes_Compile._IError> GenerateRandom(ComAmazonawsKmsTypes_Compile._IGenerateRandomRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGetKeyPolicyResponse, ComAmazonawsKmsTypes_Compile._IError> GetKeyPolicy(ComAmazonawsKmsTypes_Compile._IGetKeyPolicyRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusResponse, ComAmazonawsKmsTypes_Compile._IError> GetKeyRotationStatus(ComAmazonawsKmsTypes_Compile._IGetKeyRotationStatusRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGetParametersForImportResponse, ComAmazonawsKmsTypes_Compile._IError> GetParametersForImport(ComAmazonawsKmsTypes_Compile._IGetParametersForImportRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IGetPublicKeyResponse, ComAmazonawsKmsTypes_Compile._IError> GetPublicKey(ComAmazonawsKmsTypes_Compile._IGetPublicKeyRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IImportKeyMaterialResponse, ComAmazonawsKmsTypes_Compile._IError> ImportKeyMaterial(ComAmazonawsKmsTypes_Compile._IImportKeyMaterialRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IListAliasesResponse, ComAmazonawsKmsTypes_Compile._IError> ListAliases(ComAmazonawsKmsTypes_Compile._IListAliasesRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IListGrantsResponse, ComAmazonawsKmsTypes_Compile._IError> ListGrants(ComAmazonawsKmsTypes_Compile._IListGrantsRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IListKeyPoliciesResponse, ComAmazonawsKmsTypes_Compile._IError> ListKeyPolicies(ComAmazonawsKmsTypes_Compile._IListKeyPoliciesRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IListResourceTagsResponse, ComAmazonawsKmsTypes_Compile._IError> ListResourceTags(ComAmazonawsKmsTypes_Compile._IListResourceTagsRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> PutKeyPolicy(ComAmazonawsKmsTypes_Compile._IPutKeyPolicyRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IReEncryptResponse, ComAmazonawsKmsTypes_Compile._IError> ReEncrypt(ComAmazonawsKmsTypes_Compile._IReEncryptRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IReplicateKeyResponse, ComAmazonawsKmsTypes_Compile._IError> ReplicateKey(ComAmazonawsKmsTypes_Compile._IReplicateKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> RetireGrant(ComAmazonawsKmsTypes_Compile._IRetireGrantRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> RevokeGrant(ComAmazonawsKmsTypes_Compile._IRevokeGrantRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionResponse, ComAmazonawsKmsTypes_Compile._IError> ScheduleKeyDeletion(ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._ISignResponse, ComAmazonawsKmsTypes_Compile._IError> Sign(ComAmazonawsKmsTypes_Compile._ISignRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> TagResource(ComAmazonawsKmsTypes_Compile._ITagResourceRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> UntagResource(ComAmazonawsKmsTypes_Compile._IUntagResourceRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> UpdateAlias(ComAmazonawsKmsTypes_Compile._IUpdateAliasRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreResponse, ComAmazonawsKmsTypes_Compile._IError> UpdateCustomKeyStore(ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> UpdateKeyDescription(ComAmazonawsKmsTypes_Compile._IUpdateKeyDescriptionRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, ComAmazonawsKmsTypes_Compile._IError> UpdatePrimaryRegion(ComAmazonawsKmsTypes_Compile._IUpdatePrimaryRegionRequest input);
    Wrappers_Compile._IResult<ComAmazonawsKmsTypes_Compile._IVerifyResponse, ComAmazonawsKmsTypes_Compile._IError> Verify(ComAmazonawsKmsTypes_Compile._IVerifyRequest input);
  }
  public class _Companion_IKeyManagementServiceClient {
  }

  public interface _IKeyManagerType {
    bool is_AWS { get; }
    bool is_CUSTOMER { get; }
    _IKeyManagerType DowncastClone();
  }
  public abstract class KeyManagerType : _IKeyManagerType {
    public KeyManagerType() { }
    private static readonly _IKeyManagerType theDefault = create_AWS();
    public static _IKeyManagerType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyManagerType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyManagerType>(ComAmazonawsKmsTypes_Compile.KeyManagerType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyManagerType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyManagerType create_AWS() {
      return new KeyManagerType_AWS();
    }
    public static _IKeyManagerType create_CUSTOMER() {
      return new KeyManagerType_CUSTOMER();
    }
    public bool is_AWS { get { return this is KeyManagerType_AWS; } }
    public bool is_CUSTOMER { get { return this is KeyManagerType_CUSTOMER; } }
    public static System.Collections.Generic.IEnumerable<_IKeyManagerType> AllSingletonConstructors {
      get {
        yield return KeyManagerType.create_AWS();
        yield return KeyManagerType.create_CUSTOMER();
      }
    }
    public abstract _IKeyManagerType DowncastClone();
  }
  public class KeyManagerType_AWS : KeyManagerType {
    public KeyManagerType_AWS() {
    }
    public override _IKeyManagerType DowncastClone() {
      if (this is _IKeyManagerType dt) { return dt; }
      return new KeyManagerType_AWS();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyManagerType_AWS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyManagerType.AWS";
      return s;
    }
  }
  public class KeyManagerType_CUSTOMER : KeyManagerType {
    public KeyManagerType_CUSTOMER() {
    }
    public override _IKeyManagerType DowncastClone() {
      if (this is _IKeyManagerType dt) { return dt; }
      return new KeyManagerType_CUSTOMER();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyManagerType_CUSTOMER;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyManagerType.CUSTOMER";
      return s;
    }
  }

  public interface _IKeyMetadata {
    bool is_KeyMetadata { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AWSAccountId { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    Wrappers_Compile._IOption<bool> dtor_Enabled { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> dtor_KeyUsage { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> dtor_KeyState { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> dtor_Origin { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> dtor_ExpirationModel { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyManagerType> dtor_KeyManager { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> dtor_SigningAlgorithms { get; }
    Wrappers_Compile._IOption<bool> dtor_MultiRegion { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration> dtor_MultiRegionConfiguration { get; }
    Wrappers_Compile._IOption<int> dtor_PendingDeletionWindowInDays { get; }
    _IKeyMetadata DowncastClone();
  }
  public class KeyMetadata : _IKeyMetadata {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> AWSAccountId;
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate;
    public readonly Wrappers_Compile._IOption<bool> Enabled;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Description;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> KeyState;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> Origin;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> ExpirationModel;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyManagerType> KeyManager;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> EncryptionAlgorithms;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> SigningAlgorithms;
    public readonly Wrappers_Compile._IOption<bool> MultiRegion;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration> MultiRegionConfiguration;
    public readonly Wrappers_Compile._IOption<int> PendingDeletionWindowInDays;
    public KeyMetadata(Wrappers_Compile._IOption<Dafny.ISequence<char>> AWSAccountId, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<bool> Enabled, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> KeyState, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> ExpirationModel, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyManagerType> KeyManager, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> SigningAlgorithms, Wrappers_Compile._IOption<bool> MultiRegion, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration> MultiRegionConfiguration, Wrappers_Compile._IOption<int> PendingDeletionWindowInDays) {
      this.AWSAccountId = AWSAccountId;
      this.KeyId = KeyId;
      this.Arn = Arn;
      this.CreationDate = CreationDate;
      this.Enabled = Enabled;
      this.Description = Description;
      this.KeyUsage = KeyUsage;
      this.KeyState = KeyState;
      this.DeletionDate = DeletionDate;
      this.ValidTo = ValidTo;
      this.Origin = Origin;
      this.CustomKeyStoreId = CustomKeyStoreId;
      this.CloudHsmClusterId = CloudHsmClusterId;
      this.ExpirationModel = ExpirationModel;
      this.KeyManager = KeyManager;
      this.CustomerMasterKeySpec = CustomerMasterKeySpec;
      this.KeySpec = KeySpec;
      this.EncryptionAlgorithms = EncryptionAlgorithms;
      this.SigningAlgorithms = SigningAlgorithms;
      this.MultiRegion = MultiRegion;
      this.MultiRegionConfiguration = MultiRegionConfiguration;
      this.PendingDeletionWindowInDays = PendingDeletionWindowInDays;
    }
    public _IKeyMetadata DowncastClone() {
      if (this is _IKeyMetadata dt) { return dt; }
      return new KeyMetadata(AWSAccountId, KeyId, Arn, CreationDate, Enabled, Description, KeyUsage, KeyState, DeletionDate, ValidTo, Origin, CustomKeyStoreId, CloudHsmClusterId, ExpirationModel, KeyManager, CustomerMasterKeySpec, KeySpec, EncryptionAlgorithms, SigningAlgorithms, MultiRegion, MultiRegionConfiguration, PendingDeletionWindowInDays);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyMetadata;
      return oth != null && object.Equals(this.AWSAccountId, oth.AWSAccountId) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Arn, oth.Arn) && object.Equals(this.CreationDate, oth.CreationDate) && object.Equals(this.Enabled, oth.Enabled) && object.Equals(this.Description, oth.Description) && object.Equals(this.KeyUsage, oth.KeyUsage) && object.Equals(this.KeyState, oth.KeyState) && object.Equals(this.DeletionDate, oth.DeletionDate) && object.Equals(this.ValidTo, oth.ValidTo) && object.Equals(this.Origin, oth.Origin) && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId) && object.Equals(this.CloudHsmClusterId, oth.CloudHsmClusterId) && object.Equals(this.ExpirationModel, oth.ExpirationModel) && object.Equals(this.KeyManager, oth.KeyManager) && object.Equals(this.CustomerMasterKeySpec, oth.CustomerMasterKeySpec) && object.Equals(this.KeySpec, oth.KeySpec) && object.Equals(this.EncryptionAlgorithms, oth.EncryptionAlgorithms) && object.Equals(this.SigningAlgorithms, oth.SigningAlgorithms) && object.Equals(this.MultiRegion, oth.MultiRegion) && object.Equals(this.MultiRegionConfiguration, oth.MultiRegionConfiguration) && object.Equals(this.PendingDeletionWindowInDays, oth.PendingDeletionWindowInDays);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.AWSAccountId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Arn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CreationDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Enabled));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyUsage));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.DeletionDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ValidTo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Origin));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CloudHsmClusterId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ExpirationModel));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyManager));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomerMasterKeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.EncryptionAlgorithms));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SigningAlgorithms));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.MultiRegion));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.MultiRegionConfiguration));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PendingDeletionWindowInDays));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyMetadata.KeyMetadata";
      s += "(";
      s += Dafny.Helpers.ToString(this.AWSAccountId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Arn);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CreationDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Enabled);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Description);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyUsage);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyState);
      s += ", ";
      s += Dafny.Helpers.ToString(this.DeletionDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ValidTo);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Origin);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CloudHsmClusterId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ExpirationModel);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyManager);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CustomerMasterKeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this.EncryptionAlgorithms);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SigningAlgorithms);
      s += ", ";
      s += Dafny.Helpers.ToString(this.MultiRegion);
      s += ", ";
      s += Dafny.Helpers.ToString(this.MultiRegionConfiguration);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PendingDeletionWindowInDays);
      s += ")";
      return s;
    }
    private static readonly _IKeyMetadata theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyUsageType>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyState>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IOriginType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IExpirationModelType>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyManagerType>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeySpec>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration>.Default(), Wrappers_Compile.Option<int>.Default());
    public static _IKeyMetadata Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyMetadata> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyMetadata>(ComAmazonawsKmsTypes_Compile.KeyMetadata.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyMetadata> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyMetadata create(Wrappers_Compile._IOption<Dafny.ISequence<char>> AWSAccountId, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<bool> Enabled, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> KeyState, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> ExpirationModel, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyManagerType> KeyManager, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> SigningAlgorithms, Wrappers_Compile._IOption<bool> MultiRegion, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration> MultiRegionConfiguration, Wrappers_Compile._IOption<int> PendingDeletionWindowInDays) {
      return new KeyMetadata(AWSAccountId, KeyId, Arn, CreationDate, Enabled, Description, KeyUsage, KeyState, DeletionDate, ValidTo, Origin, CustomKeyStoreId, CloudHsmClusterId, ExpirationModel, KeyManager, CustomerMasterKeySpec, KeySpec, EncryptionAlgorithms, SigningAlgorithms, MultiRegion, MultiRegionConfiguration, PendingDeletionWindowInDays);
    }
    public bool is_KeyMetadata { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AWSAccountId {
      get {
        return this.AWSAccountId;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn {
      get {
        return this.Arn;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this.CreationDate;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Enabled {
      get {
        return this.Enabled;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description {
      get {
        return this.Description;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyUsageType> dtor_KeyUsage {
      get {
        return this.KeyUsage;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> dtor_KeyState {
      get {
        return this.KeyState;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate {
      get {
        return this.DeletionDate;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo {
      get {
        return this.ValidTo;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IOriginType> dtor_Origin {
      get {
        return this.Origin;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId {
      get {
        return this.CloudHsmClusterId;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IExpirationModelType> dtor_ExpirationModel {
      get {
        return this.ExpirationModel;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyManagerType> dtor_KeyManager {
      get {
        return this.KeyManager;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec {
      get {
        return this.CustomerMasterKeySpec;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeySpec> dtor_KeySpec {
      get {
        return this.KeySpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms {
      get {
        return this.EncryptionAlgorithms;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>> dtor_SigningAlgorithms {
      get {
        return this.SigningAlgorithms;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_MultiRegion {
      get {
        return this.MultiRegion;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration> dtor_MultiRegionConfiguration {
      get {
        return this.MultiRegionConfiguration;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_PendingDeletionWindowInDays {
      get {
        return this.PendingDeletionWindowInDays;
      }
    }
  }

  public interface _IKeySpec {
    bool is_RSA__2048 { get; }
    bool is_RSA__3072 { get; }
    bool is_RSA__4096 { get; }
    bool is_ECC__NIST__P256 { get; }
    bool is_ECC__NIST__P384 { get; }
    bool is_ECC__NIST__P521 { get; }
    bool is_ECC__SECG__P256K1 { get; }
    bool is_SYMMETRIC__DEFAULT { get; }
    _IKeySpec DowncastClone();
  }
  public abstract class KeySpec : _IKeySpec {
    public KeySpec() { }
    private static readonly _IKeySpec theDefault = create_RSA__2048();
    public static _IKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeySpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeySpec>(ComAmazonawsKmsTypes_Compile.KeySpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeySpec create_RSA__2048() {
      return new KeySpec_RSA__2048();
    }
    public static _IKeySpec create_RSA__3072() {
      return new KeySpec_RSA__3072();
    }
    public static _IKeySpec create_RSA__4096() {
      return new KeySpec_RSA__4096();
    }
    public static _IKeySpec create_ECC__NIST__P256() {
      return new KeySpec_ECC__NIST__P256();
    }
    public static _IKeySpec create_ECC__NIST__P384() {
      return new KeySpec_ECC__NIST__P384();
    }
    public static _IKeySpec create_ECC__NIST__P521() {
      return new KeySpec_ECC__NIST__P521();
    }
    public static _IKeySpec create_ECC__SECG__P256K1() {
      return new KeySpec_ECC__SECG__P256K1();
    }
    public static _IKeySpec create_SYMMETRIC__DEFAULT() {
      return new KeySpec_SYMMETRIC__DEFAULT();
    }
    public bool is_RSA__2048 { get { return this is KeySpec_RSA__2048; } }
    public bool is_RSA__3072 { get { return this is KeySpec_RSA__3072; } }
    public bool is_RSA__4096 { get { return this is KeySpec_RSA__4096; } }
    public bool is_ECC__NIST__P256 { get { return this is KeySpec_ECC__NIST__P256; } }
    public bool is_ECC__NIST__P384 { get { return this is KeySpec_ECC__NIST__P384; } }
    public bool is_ECC__NIST__P521 { get { return this is KeySpec_ECC__NIST__P521; } }
    public bool is_ECC__SECG__P256K1 { get { return this is KeySpec_ECC__SECG__P256K1; } }
    public bool is_SYMMETRIC__DEFAULT { get { return this is KeySpec_SYMMETRIC__DEFAULT; } }
    public static System.Collections.Generic.IEnumerable<_IKeySpec> AllSingletonConstructors {
      get {
        yield return KeySpec.create_RSA__2048();
        yield return KeySpec.create_RSA__3072();
        yield return KeySpec.create_RSA__4096();
        yield return KeySpec.create_ECC__NIST__P256();
        yield return KeySpec.create_ECC__NIST__P384();
        yield return KeySpec.create_ECC__NIST__P521();
        yield return KeySpec.create_ECC__SECG__P256K1();
        yield return KeySpec.create_SYMMETRIC__DEFAULT();
      }
    }
    public abstract _IKeySpec DowncastClone();
  }
  public class KeySpec_RSA__2048 : KeySpec {
    public KeySpec_RSA__2048() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_RSA__2048();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_RSA__2048;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.RSA_2048";
      return s;
    }
  }
  public class KeySpec_RSA__3072 : KeySpec {
    public KeySpec_RSA__3072() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_RSA__3072();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_RSA__3072;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.RSA_3072";
      return s;
    }
  }
  public class KeySpec_RSA__4096 : KeySpec {
    public KeySpec_RSA__4096() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_RSA__4096();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_RSA__4096;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.RSA_4096";
      return s;
    }
  }
  public class KeySpec_ECC__NIST__P256 : KeySpec {
    public KeySpec_ECC__NIST__P256() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__NIST__P256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_ECC__NIST__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.ECC_NIST_P256";
      return s;
    }
  }
  public class KeySpec_ECC__NIST__P384 : KeySpec {
    public KeySpec_ECC__NIST__P384() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__NIST__P384();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_ECC__NIST__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.ECC_NIST_P384";
      return s;
    }
  }
  public class KeySpec_ECC__NIST__P521 : KeySpec {
    public KeySpec_ECC__NIST__P521() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__NIST__P521();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_ECC__NIST__P521;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.ECC_NIST_P521";
      return s;
    }
  }
  public class KeySpec_ECC__SECG__P256K1 : KeySpec {
    public KeySpec_ECC__SECG__P256K1() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__SECG__P256K1();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_ECC__SECG__P256K1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.ECC_SECG_P256K1";
      return s;
    }
  }
  public class KeySpec_SYMMETRIC__DEFAULT : KeySpec {
    public KeySpec_SYMMETRIC__DEFAULT() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_SYMMETRIC__DEFAULT();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeySpec_SYMMETRIC__DEFAULT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeySpec.SYMMETRIC_DEFAULT";
      return s;
    }
  }

  public interface _IKeyState {
    bool is_Creating { get; }
    bool is_Enabled { get; }
    bool is_Disabled { get; }
    bool is_PendingDeletion { get; }
    bool is_PendingImport { get; }
    bool is_PendingReplicaDeletion { get; }
    bool is_Unavailable { get; }
    bool is_Updating { get; }
    _IKeyState DowncastClone();
  }
  public abstract class KeyState : _IKeyState {
    public KeyState() { }
    private static readonly _IKeyState theDefault = create_Creating();
    public static _IKeyState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyState> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyState>(ComAmazonawsKmsTypes_Compile.KeyState.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyState create_Creating() {
      return new KeyState_Creating();
    }
    public static _IKeyState create_Enabled() {
      return new KeyState_Enabled();
    }
    public static _IKeyState create_Disabled() {
      return new KeyState_Disabled();
    }
    public static _IKeyState create_PendingDeletion() {
      return new KeyState_PendingDeletion();
    }
    public static _IKeyState create_PendingImport() {
      return new KeyState_PendingImport();
    }
    public static _IKeyState create_PendingReplicaDeletion() {
      return new KeyState_PendingReplicaDeletion();
    }
    public static _IKeyState create_Unavailable() {
      return new KeyState_Unavailable();
    }
    public static _IKeyState create_Updating() {
      return new KeyState_Updating();
    }
    public bool is_Creating { get { return this is KeyState_Creating; } }
    public bool is_Enabled { get { return this is KeyState_Enabled; } }
    public bool is_Disabled { get { return this is KeyState_Disabled; } }
    public bool is_PendingDeletion { get { return this is KeyState_PendingDeletion; } }
    public bool is_PendingImport { get { return this is KeyState_PendingImport; } }
    public bool is_PendingReplicaDeletion { get { return this is KeyState_PendingReplicaDeletion; } }
    public bool is_Unavailable { get { return this is KeyState_Unavailable; } }
    public bool is_Updating { get { return this is KeyState_Updating; } }
    public static System.Collections.Generic.IEnumerable<_IKeyState> AllSingletonConstructors {
      get {
        yield return KeyState.create_Creating();
        yield return KeyState.create_Enabled();
        yield return KeyState.create_Disabled();
        yield return KeyState.create_PendingDeletion();
        yield return KeyState.create_PendingImport();
        yield return KeyState.create_PendingReplicaDeletion();
        yield return KeyState.create_Unavailable();
        yield return KeyState.create_Updating();
      }
    }
    public abstract _IKeyState DowncastClone();
  }
  public class KeyState_Creating : KeyState {
    public KeyState_Creating() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Creating();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_Creating;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.Creating";
      return s;
    }
  }
  public class KeyState_Enabled : KeyState {
    public KeyState_Enabled() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Enabled();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_Enabled;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.Enabled";
      return s;
    }
  }
  public class KeyState_Disabled : KeyState {
    public KeyState_Disabled() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Disabled();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_Disabled;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.Disabled";
      return s;
    }
  }
  public class KeyState_PendingDeletion : KeyState {
    public KeyState_PendingDeletion() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_PendingDeletion();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_PendingDeletion;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.PendingDeletion";
      return s;
    }
  }
  public class KeyState_PendingImport : KeyState {
    public KeyState_PendingImport() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_PendingImport();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_PendingImport;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.PendingImport";
      return s;
    }
  }
  public class KeyState_PendingReplicaDeletion : KeyState {
    public KeyState_PendingReplicaDeletion() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_PendingReplicaDeletion();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_PendingReplicaDeletion;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.PendingReplicaDeletion";
      return s;
    }
  }
  public class KeyState_Unavailable : KeyState {
    public KeyState_Unavailable() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Unavailable();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_Unavailable;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.Unavailable";
      return s;
    }
  }
  public class KeyState_Updating : KeyState {
    public KeyState_Updating() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Updating();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyState_Updating;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyState.Updating";
      return s;
    }
  }

  public partial class KeyStorePasswordType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IKeyUsageType {
    bool is_SIGN__VERIFY { get; }
    bool is_ENCRYPT__DECRYPT { get; }
    _IKeyUsageType DowncastClone();
  }
  public abstract class KeyUsageType : _IKeyUsageType {
    public KeyUsageType() { }
    private static readonly _IKeyUsageType theDefault = create_SIGN__VERIFY();
    public static _IKeyUsageType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyUsageType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyUsageType>(ComAmazonawsKmsTypes_Compile.KeyUsageType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IKeyUsageType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyUsageType create_SIGN__VERIFY() {
      return new KeyUsageType_SIGN__VERIFY();
    }
    public static _IKeyUsageType create_ENCRYPT__DECRYPT() {
      return new KeyUsageType_ENCRYPT__DECRYPT();
    }
    public bool is_SIGN__VERIFY { get { return this is KeyUsageType_SIGN__VERIFY; } }
    public bool is_ENCRYPT__DECRYPT { get { return this is KeyUsageType_ENCRYPT__DECRYPT; } }
    public static System.Collections.Generic.IEnumerable<_IKeyUsageType> AllSingletonConstructors {
      get {
        yield return KeyUsageType.create_SIGN__VERIFY();
        yield return KeyUsageType.create_ENCRYPT__DECRYPT();
      }
    }
    public abstract _IKeyUsageType DowncastClone();
  }
  public class KeyUsageType_SIGN__VERIFY : KeyUsageType {
    public KeyUsageType_SIGN__VERIFY() {
    }
    public override _IKeyUsageType DowncastClone() {
      if (this is _IKeyUsageType dt) { return dt; }
      return new KeyUsageType_SIGN__VERIFY();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyUsageType_SIGN__VERIFY;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyUsageType.SIGN_VERIFY";
      return s;
    }
  }
  public class KeyUsageType_ENCRYPT__DECRYPT : KeyUsageType {
    public KeyUsageType_ENCRYPT__DECRYPT() {
    }
    public override _IKeyUsageType DowncastClone() {
      if (this is _IKeyUsageType dt) { return dt; }
      return new KeyUsageType_ENCRYPT__DECRYPT();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.KeyUsageType_ENCRYPT__DECRYPT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.KeyUsageType.ENCRYPT_DECRYPT";
      return s;
    }
  }

  public partial class LimitType {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IListAliasesRequest {
    bool is_ListAliasesRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListAliasesRequest DowncastClone();
  }
  public class ListAliasesRequest : _IListAliasesRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<int> Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker;
    public ListAliasesRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this.KeyId = KeyId;
      this.Limit = Limit;
      this.Marker = Marker;
    }
    public _IListAliasesRequest DowncastClone() {
      if (this is _IListAliasesRequest dt) { return dt; }
      return new ListAliasesRequest(KeyId, Limit, Marker);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListAliasesRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Limit, oth.Limit) && object.Equals(this.Marker, oth.Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListAliasesRequest.ListAliasesRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Marker);
      s += ")";
      return s;
    }
    private static readonly _IListAliasesRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IListAliasesRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListAliasesRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListAliasesRequest>(ComAmazonawsKmsTypes_Compile.ListAliasesRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListAliasesRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListAliasesRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListAliasesRequest(KeyId, Limit, Marker);
    }
    public bool is_ListAliasesRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this.Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this.Marker;
      }
    }
  }

  public interface _IListAliasesResponse {
    bool is_ListAliasesResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IAliasListEntry>> dtor_Aliases { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListAliasesResponse DowncastClone();
  }
  public class ListAliasesResponse : _IListAliasesResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IAliasListEntry>> Aliases;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker;
    public readonly Wrappers_Compile._IOption<bool> Truncated;
    public ListAliasesResponse(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IAliasListEntry>> Aliases, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this.Aliases = Aliases;
      this.NextMarker = NextMarker;
      this.Truncated = Truncated;
    }
    public _IListAliasesResponse DowncastClone() {
      if (this is _IListAliasesResponse dt) { return dt; }
      return new ListAliasesResponse(Aliases, NextMarker, Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListAliasesResponse;
      return oth != null && object.Equals(this.Aliases, oth.Aliases) && object.Equals(this.NextMarker, oth.NextMarker) && object.Equals(this.Truncated, oth.Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Aliases));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListAliasesResponse.ListAliasesResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.Aliases);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Truncated);
      s += ")";
      return s;
    }
    private static readonly _IListAliasesResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IAliasListEntry>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static _IListAliasesResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListAliasesResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListAliasesResponse>(ComAmazonawsKmsTypes_Compile.ListAliasesResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListAliasesResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListAliasesResponse create(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IAliasListEntry>> Aliases, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListAliasesResponse(Aliases, NextMarker, Truncated);
    }
    public bool is_ListAliasesResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IAliasListEntry>> dtor_Aliases {
      get {
        return this.Aliases;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this.NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this.Truncated;
      }
    }
  }

  public interface _IListGrantsRequest {
    bool is_ListGrantsRequest { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal { get; }
    _IListGrantsRequest DowncastClone();
  }
  public class ListGrantsRequest : _IListGrantsRequest {
    public readonly Wrappers_Compile._IOption<int> Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker;
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal;
    public ListGrantsRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal) {
      this.Limit = Limit;
      this.Marker = Marker;
      this.KeyId = KeyId;
      this.GrantId = GrantId;
      this.GranteePrincipal = GranteePrincipal;
    }
    public _IListGrantsRequest DowncastClone() {
      if (this is _IListGrantsRequest dt) { return dt; }
      return new ListGrantsRequest(Limit, Marker, KeyId, GrantId, GranteePrincipal);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListGrantsRequest;
      return oth != null && object.Equals(this.Limit, oth.Limit) && object.Equals(this.Marker, oth.Marker) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.GrantId, oth.GrantId) && object.Equals(this.GranteePrincipal, oth.GranteePrincipal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Marker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GranteePrincipal));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListGrantsRequest.ListGrantsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Marker);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GranteePrincipal);
      s += ")";
      return s;
    }
    private static readonly _IListGrantsRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IListGrantsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListGrantsRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListGrantsRequest>(ComAmazonawsKmsTypes_Compile.ListGrantsRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListGrantsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListGrantsRequest create(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal) {
      return new ListGrantsRequest(Limit, Marker, KeyId, GrantId, GranteePrincipal);
    }
    public bool is_ListGrantsRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this.Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this.Marker;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this.GrantId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal {
      get {
        return this.GranteePrincipal;
      }
    }
  }

  public interface _IListGrantsResponse {
    bool is_ListGrantsResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantListEntry>> dtor_Grants { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListGrantsResponse DowncastClone();
  }
  public class ListGrantsResponse : _IListGrantsResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantListEntry>> Grants;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker;
    public readonly Wrappers_Compile._IOption<bool> Truncated;
    public ListGrantsResponse(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantListEntry>> Grants, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this.Grants = Grants;
      this.NextMarker = NextMarker;
      this.Truncated = Truncated;
    }
    public _IListGrantsResponse DowncastClone() {
      if (this is _IListGrantsResponse dt) { return dt; }
      return new ListGrantsResponse(Grants, NextMarker, Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListGrantsResponse;
      return oth != null && object.Equals(this.Grants, oth.Grants) && object.Equals(this.NextMarker, oth.NextMarker) && object.Equals(this.Truncated, oth.Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Grants));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListGrantsResponse.ListGrantsResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.Grants);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Truncated);
      s += ")";
      return s;
    }
    private static readonly _IListGrantsResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantListEntry>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static _IListGrantsResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListGrantsResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListGrantsResponse>(ComAmazonawsKmsTypes_Compile.ListGrantsResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListGrantsResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListGrantsResponse create(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantListEntry>> Grants, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListGrantsResponse(Grants, NextMarker, Truncated);
    }
    public bool is_ListGrantsResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IGrantListEntry>> dtor_Grants {
      get {
        return this.Grants;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this.NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this.Truncated;
      }
    }
  }

  public interface _IListKeyPoliciesRequest {
    bool is_ListKeyPoliciesRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListKeyPoliciesRequest DowncastClone();
  }
  public class ListKeyPoliciesRequest : _IListKeyPoliciesRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<int> Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker;
    public ListKeyPoliciesRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this.KeyId = KeyId;
      this.Limit = Limit;
      this.Marker = Marker;
    }
    public _IListKeyPoliciesRequest DowncastClone() {
      if (this is _IListKeyPoliciesRequest dt) { return dt; }
      return new ListKeyPoliciesRequest(KeyId, Limit, Marker);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListKeyPoliciesRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Limit, oth.Limit) && object.Equals(this.Marker, oth.Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListKeyPoliciesRequest.ListKeyPoliciesRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Marker);
      s += ")";
      return s;
    }
    private static readonly _IListKeyPoliciesRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IListKeyPoliciesRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeyPoliciesRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeyPoliciesRequest>(ComAmazonawsKmsTypes_Compile.ListKeyPoliciesRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeyPoliciesRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListKeyPoliciesRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListKeyPoliciesRequest(KeyId, Limit, Marker);
    }
    public bool is_ListKeyPoliciesRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this.Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this.Marker;
      }
    }
  }

  public interface _IListKeyPoliciesResponse {
    bool is_ListKeyPoliciesResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_PolicyNames { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListKeyPoliciesResponse DowncastClone();
  }
  public class ListKeyPoliciesResponse : _IListKeyPoliciesResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> PolicyNames;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker;
    public readonly Wrappers_Compile._IOption<bool> Truncated;
    public ListKeyPoliciesResponse(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> PolicyNames, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this.PolicyNames = PolicyNames;
      this.NextMarker = NextMarker;
      this.Truncated = Truncated;
    }
    public _IListKeyPoliciesResponse DowncastClone() {
      if (this is _IListKeyPoliciesResponse dt) { return dt; }
      return new ListKeyPoliciesResponse(PolicyNames, NextMarker, Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListKeyPoliciesResponse;
      return oth != null && object.Equals(this.PolicyNames, oth.PolicyNames) && object.Equals(this.NextMarker, oth.NextMarker) && object.Equals(this.Truncated, oth.Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PolicyNames));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListKeyPoliciesResponse.ListKeyPoliciesResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.PolicyNames);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Truncated);
      s += ")";
      return s;
    }
    private static readonly _IListKeyPoliciesResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static _IListKeyPoliciesResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeyPoliciesResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeyPoliciesResponse>(ComAmazonawsKmsTypes_Compile.ListKeyPoliciesResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeyPoliciesResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListKeyPoliciesResponse create(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> PolicyNames, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListKeyPoliciesResponse(PolicyNames, NextMarker, Truncated);
    }
    public bool is_ListKeyPoliciesResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_PolicyNames {
      get {
        return this.PolicyNames;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this.NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this.Truncated;
      }
    }
  }

  public interface _IListKeysRequest {
    bool is_ListKeysRequest { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListKeysRequest DowncastClone();
  }
  public class ListKeysRequest : _IListKeysRequest {
    public readonly Wrappers_Compile._IOption<int> Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker;
    public ListKeysRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this.Limit = Limit;
      this.Marker = Marker;
    }
    public _IListKeysRequest DowncastClone() {
      if (this is _IListKeysRequest dt) { return dt; }
      return new ListKeysRequest(Limit, Marker);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListKeysRequest;
      return oth != null && object.Equals(this.Limit, oth.Limit) && object.Equals(this.Marker, oth.Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListKeysRequest.ListKeysRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Marker);
      s += ")";
      return s;
    }
    private static readonly _IListKeysRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IListKeysRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeysRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeysRequest>(ComAmazonawsKmsTypes_Compile.ListKeysRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListKeysRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListKeysRequest create(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListKeysRequest(Limit, Marker);
    }
    public bool is_ListKeysRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this.Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this.Marker;
      }
    }
  }

  public interface _IListResourceTagsRequest {
    bool is_ListResourceTagsRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListResourceTagsRequest DowncastClone();
  }
  public class ListResourceTagsRequest : _IListResourceTagsRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<int> Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker;
    public ListResourceTagsRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this.KeyId = KeyId;
      this.Limit = Limit;
      this.Marker = Marker;
    }
    public _IListResourceTagsRequest DowncastClone() {
      if (this is _IListResourceTagsRequest dt) { return dt; }
      return new ListResourceTagsRequest(KeyId, Limit, Marker);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListResourceTagsRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Limit, oth.Limit) && object.Equals(this.Marker, oth.Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListResourceTagsRequest.ListResourceTagsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Marker);
      s += ")";
      return s;
    }
    private static readonly _IListResourceTagsRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IListResourceTagsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListResourceTagsRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListResourceTagsRequest>(ComAmazonawsKmsTypes_Compile.ListResourceTagsRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListResourceTagsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListResourceTagsRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListResourceTagsRequest(KeyId, Limit, Marker);
    }
    public bool is_ListResourceTagsRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this.Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this.Marker;
      }
    }
  }

  public interface _IListResourceTagsResponse {
    bool is_ListResourceTagsResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_Tags { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListResourceTagsResponse DowncastClone();
  }
  public class ListResourceTagsResponse : _IListResourceTagsResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker;
    public readonly Wrappers_Compile._IOption<bool> Truncated;
    public ListResourceTagsResponse(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this.Tags = Tags;
      this.NextMarker = NextMarker;
      this.Truncated = Truncated;
    }
    public _IListResourceTagsResponse DowncastClone() {
      if (this is _IListResourceTagsResponse dt) { return dt; }
      return new ListResourceTagsResponse(Tags, NextMarker, Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListResourceTagsResponse;
      return oth != null && object.Equals(this.Tags, oth.Tags) && object.Equals(this.NextMarker, oth.NextMarker) && object.Equals(this.Truncated, oth.Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Tags));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListResourceTagsResponse.ListResourceTagsResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.Tags);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Truncated);
      s += ")";
      return s;
    }
    private static readonly _IListResourceTagsResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static _IListResourceTagsResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListResourceTagsResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListResourceTagsResponse>(ComAmazonawsKmsTypes_Compile.ListResourceTagsResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListResourceTagsResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListResourceTagsResponse create(Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListResourceTagsResponse(Tags, NextMarker, Truncated);
    }
    public bool is_ListResourceTagsResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_Tags {
      get {
        return this.Tags;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this.NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this.Truncated;
      }
    }
  }

  public interface _IListRetirableGrantsRequest {
    bool is_ListRetirableGrantsRequest { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    Dafny.ISequence<char> dtor_RetiringPrincipal { get; }
    _IListRetirableGrantsRequest DowncastClone();
  }
  public class ListRetirableGrantsRequest : _IListRetirableGrantsRequest {
    public readonly Wrappers_Compile._IOption<int> Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker;
    public readonly Dafny.ISequence<char> RetiringPrincipal;
    public ListRetirableGrantsRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> RetiringPrincipal) {
      this.Limit = Limit;
      this.Marker = Marker;
      this.RetiringPrincipal = RetiringPrincipal;
    }
    public _IListRetirableGrantsRequest DowncastClone() {
      if (this is _IListRetirableGrantsRequest dt) { return dt; }
      return new ListRetirableGrantsRequest(Limit, Marker, RetiringPrincipal);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ListRetirableGrantsRequest;
      return oth != null && object.Equals(this.Limit, oth.Limit) && object.Equals(this.Marker, oth.Marker) && object.Equals(this.RetiringPrincipal, oth.RetiringPrincipal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Marker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.RetiringPrincipal));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ListRetirableGrantsRequest.ListRetirableGrantsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Marker);
      s += ", ";
      s += Dafny.Helpers.ToString(this.RetiringPrincipal);
      s += ")";
      return s;
    }
    private static readonly _IListRetirableGrantsRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty);
    public static _IListRetirableGrantsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListRetirableGrantsRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListRetirableGrantsRequest>(ComAmazonawsKmsTypes_Compile.ListRetirableGrantsRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IListRetirableGrantsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListRetirableGrantsRequest create(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> RetiringPrincipal) {
      return new ListRetirableGrantsRequest(Limit, Marker, RetiringPrincipal);
    }
    public bool is_ListRetirableGrantsRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this.Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this.Marker;
      }
    }
    public Dafny.ISequence<char> dtor_RetiringPrincipal {
      get {
        return this.RetiringPrincipal;
      }
    }
  }

  public partial class MarkerType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IMessageType {
    bool is_RAW { get; }
    bool is_DIGEST { get; }
    _IMessageType DowncastClone();
  }
  public abstract class MessageType : _IMessageType {
    public MessageType() { }
    private static readonly _IMessageType theDefault = create_RAW();
    public static _IMessageType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMessageType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMessageType>(ComAmazonawsKmsTypes_Compile.MessageType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMessageType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMessageType create_RAW() {
      return new MessageType_RAW();
    }
    public static _IMessageType create_DIGEST() {
      return new MessageType_DIGEST();
    }
    public bool is_RAW { get { return this is MessageType_RAW; } }
    public bool is_DIGEST { get { return this is MessageType_DIGEST; } }
    public static System.Collections.Generic.IEnumerable<_IMessageType> AllSingletonConstructors {
      get {
        yield return MessageType.create_RAW();
        yield return MessageType.create_DIGEST();
      }
    }
    public abstract _IMessageType DowncastClone();
  }
  public class MessageType_RAW : MessageType {
    public MessageType_RAW() {
    }
    public override _IMessageType DowncastClone() {
      if (this is _IMessageType dt) { return dt; }
      return new MessageType_RAW();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.MessageType_RAW;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.MessageType.RAW";
      return s;
    }
  }
  public class MessageType_DIGEST : MessageType {
    public MessageType_DIGEST() {
    }
    public override _IMessageType DowncastClone() {
      if (this is _IMessageType dt) { return dt; }
      return new MessageType_DIGEST();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.MessageType_DIGEST;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.MessageType.DIGEST";
      return s;
    }
  }

  public interface _IMultiRegionConfiguration {
    bool is_MultiRegionConfiguration { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType> dtor_MultiRegionKeyType { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKey> dtor_PrimaryKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>> dtor_ReplicaKeys { get; }
    _IMultiRegionConfiguration DowncastClone();
  }
  public class MultiRegionConfiguration : _IMultiRegionConfiguration {
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType> MultiRegionKeyType;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKey> PrimaryKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>> ReplicaKeys;
    public MultiRegionConfiguration(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType> MultiRegionKeyType, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKey> PrimaryKey, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>> ReplicaKeys) {
      this.MultiRegionKeyType = MultiRegionKeyType;
      this.PrimaryKey = PrimaryKey;
      this.ReplicaKeys = ReplicaKeys;
    }
    public _IMultiRegionConfiguration DowncastClone() {
      if (this is _IMultiRegionConfiguration dt) { return dt; }
      return new MultiRegionConfiguration(MultiRegionKeyType, PrimaryKey, ReplicaKeys);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.MultiRegionConfiguration;
      return oth != null && object.Equals(this.MultiRegionKeyType, oth.MultiRegionKeyType) && object.Equals(this.PrimaryKey, oth.PrimaryKey) && object.Equals(this.ReplicaKeys, oth.ReplicaKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.MultiRegionKeyType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PrimaryKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ReplicaKeys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.MultiRegionConfiguration.MultiRegionConfiguration";
      s += "(";
      s += Dafny.Helpers.ToString(this.MultiRegionKeyType);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PrimaryKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ReplicaKeys);
      s += ")";
      return s;
    }
    private static readonly _IMultiRegionConfiguration theDefault = create(Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>>.Default());
    public static _IMultiRegionConfiguration Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration>(ComAmazonawsKmsTypes_Compile.MultiRegionConfiguration.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionConfiguration> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMultiRegionConfiguration create(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType> MultiRegionKeyType, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKey> PrimaryKey, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>> ReplicaKeys) {
      return new MultiRegionConfiguration(MultiRegionKeyType, PrimaryKey, ReplicaKeys);
    }
    public bool is_MultiRegionConfiguration { get { return true; } }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType> dtor_MultiRegionKeyType {
      get {
        return this.MultiRegionKeyType;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMultiRegionKey> dtor_PrimaryKey {
      get {
        return this.PrimaryKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>> dtor_ReplicaKeys {
      get {
        return this.ReplicaKeys;
      }
    }
  }

  public interface _IMultiRegionKey {
    bool is_MultiRegionKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Region { get; }
    _IMultiRegionKey DowncastClone();
  }
  public class MultiRegionKey : _IMultiRegionKey {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Region;
    public MultiRegionKey(Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> Region) {
      this.Arn = Arn;
      this.Region = Region;
    }
    public _IMultiRegionKey DowncastClone() {
      if (this is _IMultiRegionKey dt) { return dt; }
      return new MultiRegionKey(Arn, Region);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.MultiRegionKey;
      return oth != null && object.Equals(this.Arn, oth.Arn) && object.Equals(this.Region, oth.Region);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Arn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Region));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.MultiRegionKey.MultiRegionKey";
      s += "(";
      s += Dafny.Helpers.ToString(this.Arn);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Region);
      s += ")";
      return s;
    }
    private static readonly _IMultiRegionKey theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IMultiRegionKey Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionKey> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionKey>(ComAmazonawsKmsTypes_Compile.MultiRegionKey.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionKey> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMultiRegionKey create(Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> Region) {
      return new MultiRegionKey(Arn, Region);
    }
    public bool is_MultiRegionKey { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn {
      get {
        return this.Arn;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Region {
      get {
        return this.Region;
      }
    }
  }

  public interface _IMultiRegionKeyType {
    bool is_PRIMARY { get; }
    bool is_REPLICA { get; }
    _IMultiRegionKeyType DowncastClone();
  }
  public abstract class MultiRegionKeyType : _IMultiRegionKeyType {
    public MultiRegionKeyType() { }
    private static readonly _IMultiRegionKeyType theDefault = create_PRIMARY();
    public static _IMultiRegionKeyType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType>(ComAmazonawsKmsTypes_Compile.MultiRegionKeyType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IMultiRegionKeyType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMultiRegionKeyType create_PRIMARY() {
      return new MultiRegionKeyType_PRIMARY();
    }
    public static _IMultiRegionKeyType create_REPLICA() {
      return new MultiRegionKeyType_REPLICA();
    }
    public bool is_PRIMARY { get { return this is MultiRegionKeyType_PRIMARY; } }
    public bool is_REPLICA { get { return this is MultiRegionKeyType_REPLICA; } }
    public static System.Collections.Generic.IEnumerable<_IMultiRegionKeyType> AllSingletonConstructors {
      get {
        yield return MultiRegionKeyType.create_PRIMARY();
        yield return MultiRegionKeyType.create_REPLICA();
      }
    }
    public abstract _IMultiRegionKeyType DowncastClone();
  }
  public class MultiRegionKeyType_PRIMARY : MultiRegionKeyType {
    public MultiRegionKeyType_PRIMARY() {
    }
    public override _IMultiRegionKeyType DowncastClone() {
      if (this is _IMultiRegionKeyType dt) { return dt; }
      return new MultiRegionKeyType_PRIMARY();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.MultiRegionKeyType_PRIMARY;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.MultiRegionKeyType.PRIMARY";
      return s;
    }
  }
  public class MultiRegionKeyType_REPLICA : MultiRegionKeyType {
    public MultiRegionKeyType_REPLICA() {
    }
    public override _IMultiRegionKeyType DowncastClone() {
      if (this is _IMultiRegionKeyType dt) { return dt; }
      return new MultiRegionKeyType_REPLICA();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.MultiRegionKeyType_REPLICA;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.MultiRegionKeyType.REPLICA";
      return s;
    }
  }

  public partial class NumberOfBytesType {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IOriginType {
    bool is_AWS__KMS { get; }
    bool is_EXTERNAL { get; }
    bool is_AWS__CLOUDHSM { get; }
    _IOriginType DowncastClone();
  }
  public abstract class OriginType : _IOriginType {
    public OriginType() { }
    private static readonly _IOriginType theDefault = create_AWS__KMS();
    public static _IOriginType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IOriginType> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IOriginType>(ComAmazonawsKmsTypes_Compile.OriginType.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IOriginType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOriginType create_AWS__KMS() {
      return new OriginType_AWS__KMS();
    }
    public static _IOriginType create_EXTERNAL() {
      return new OriginType_EXTERNAL();
    }
    public static _IOriginType create_AWS__CLOUDHSM() {
      return new OriginType_AWS__CLOUDHSM();
    }
    public bool is_AWS__KMS { get { return this is OriginType_AWS__KMS; } }
    public bool is_EXTERNAL { get { return this is OriginType_EXTERNAL; } }
    public bool is_AWS__CLOUDHSM { get { return this is OriginType_AWS__CLOUDHSM; } }
    public static System.Collections.Generic.IEnumerable<_IOriginType> AllSingletonConstructors {
      get {
        yield return OriginType.create_AWS__KMS();
        yield return OriginType.create_EXTERNAL();
        yield return OriginType.create_AWS__CLOUDHSM();
      }
    }
    public abstract _IOriginType DowncastClone();
  }
  public class OriginType_AWS__KMS : OriginType {
    public OriginType_AWS__KMS() {
    }
    public override _IOriginType DowncastClone() {
      if (this is _IOriginType dt) { return dt; }
      return new OriginType_AWS__KMS();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.OriginType_AWS__KMS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.OriginType.AWS_KMS";
      return s;
    }
  }
  public class OriginType_EXTERNAL : OriginType {
    public OriginType_EXTERNAL() {
    }
    public override _IOriginType DowncastClone() {
      if (this is _IOriginType dt) { return dt; }
      return new OriginType_EXTERNAL();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.OriginType_EXTERNAL;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.OriginType.EXTERNAL";
      return s;
    }
  }
  public class OriginType_AWS__CLOUDHSM : OriginType {
    public OriginType_AWS__CLOUDHSM() {
    }
    public override _IOriginType DowncastClone() {
      if (this is _IOriginType dt) { return dt; }
      return new OriginType_AWS__CLOUDHSM();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.OriginType_AWS__CLOUDHSM;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.OriginType.AWS_CLOUDHSM";
      return s;
    }
  }

  public partial class PendingWindowInDaysType {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PlaintextType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PolicyNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PolicyType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PrincipalIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PublicKeyType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IPutKeyPolicyRequest {
    bool is_PutKeyPolicyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_PolicyName { get; }
    Dafny.ISequence<char> dtor_Policy { get; }
    Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck { get; }
    _IPutKeyPolicyRequest DowncastClone();
  }
  public class PutKeyPolicyRequest : _IPutKeyPolicyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<char> PolicyName;
    public readonly Dafny.ISequence<char> Policy;
    public readonly Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck;
    public PutKeyPolicyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName, Dafny.ISequence<char> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck) {
      this.KeyId = KeyId;
      this.PolicyName = PolicyName;
      this.Policy = Policy;
      this.BypassPolicyLockoutSafetyCheck = BypassPolicyLockoutSafetyCheck;
    }
    public _IPutKeyPolicyRequest DowncastClone() {
      if (this is _IPutKeyPolicyRequest dt) { return dt; }
      return new PutKeyPolicyRequest(KeyId, PolicyName, Policy, BypassPolicyLockoutSafetyCheck);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.PutKeyPolicyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.PolicyName, oth.PolicyName) && object.Equals(this.Policy, oth.Policy) && object.Equals(this.BypassPolicyLockoutSafetyCheck, oth.BypassPolicyLockoutSafetyCheck);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PolicyName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Policy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.BypassPolicyLockoutSafetyCheck));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.PutKeyPolicyRequest.PutKeyPolicyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PolicyName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Policy);
      s += ", ";
      s += Dafny.Helpers.ToString(this.BypassPolicyLockoutSafetyCheck);
      s += ")";
      return s;
    }
    private static readonly _IPutKeyPolicyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<bool>.Default());
    public static _IPutKeyPolicyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IPutKeyPolicyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IPutKeyPolicyRequest>(ComAmazonawsKmsTypes_Compile.PutKeyPolicyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IPutKeyPolicyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPutKeyPolicyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName, Dafny.ISequence<char> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck) {
      return new PutKeyPolicyRequest(KeyId, PolicyName, Policy, BypassPolicyLockoutSafetyCheck);
    }
    public bool is_PutKeyPolicyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_PolicyName {
      get {
        return this.PolicyName;
      }
    }
    public Dafny.ISequence<char> dtor_Policy {
      get {
        return this.Policy;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck {
      get {
        return this.BypassPolicyLockoutSafetyCheck;
      }
    }
  }

  public interface _IReEncryptRequest {
    bool is_ReEncryptRequest { get; }
    Dafny.ISequence<byte> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SourceEncryptionContext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId { get; }
    Dafny.ISequence<char> dtor_DestinationKeyId { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_DestinationEncryptionContext { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IReEncryptRequest DowncastClone();
  }
  public class ReEncryptRequest : _IReEncryptRequest {
    public readonly Dafny.ISequence<byte> CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SourceEncryptionContext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId;
    public readonly Dafny.ISequence<char> DestinationKeyId;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> DestinationEncryptionContext;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public ReEncryptRequest(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SourceEncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Dafny.ISequence<char> DestinationKeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> DestinationEncryptionContext, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.CiphertextBlob = CiphertextBlob;
      this.SourceEncryptionContext = SourceEncryptionContext;
      this.SourceKeyId = SourceKeyId;
      this.DestinationKeyId = DestinationKeyId;
      this.DestinationEncryptionContext = DestinationEncryptionContext;
      this.SourceEncryptionAlgorithm = SourceEncryptionAlgorithm;
      this.DestinationEncryptionAlgorithm = DestinationEncryptionAlgorithm;
      this.GrantTokens = GrantTokens;
    }
    public _IReEncryptRequest DowncastClone() {
      if (this is _IReEncryptRequest dt) { return dt; }
      return new ReEncryptRequest(CiphertextBlob, SourceEncryptionContext, SourceKeyId, DestinationKeyId, DestinationEncryptionContext, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ReEncryptRequest;
      return oth != null && object.Equals(this.CiphertextBlob, oth.CiphertextBlob) && object.Equals(this.SourceEncryptionContext, oth.SourceEncryptionContext) && object.Equals(this.SourceKeyId, oth.SourceKeyId) && object.Equals(this.DestinationKeyId, oth.DestinationKeyId) && object.Equals(this.DestinationEncryptionContext, oth.DestinationEncryptionContext) && object.Equals(this.SourceEncryptionAlgorithm, oth.SourceEncryptionAlgorithm) && object.Equals(this.DestinationEncryptionAlgorithm, oth.DestinationEncryptionAlgorithm) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SourceEncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SourceKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.DestinationKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.DestinationEncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SourceEncryptionAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.DestinationEncryptionAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ReEncryptRequest.ReEncryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SourceEncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SourceKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.DestinationKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.DestinationEncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SourceEncryptionAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.DestinationEncryptionAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IReEncryptRequest theDefault = create(Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IReEncryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReEncryptRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReEncryptRequest>(ComAmazonawsKmsTypes_Compile.ReEncryptRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReEncryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReEncryptRequest create(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SourceEncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Dafny.ISequence<char> DestinationKeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> DestinationEncryptionContext, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new ReEncryptRequest(CiphertextBlob, SourceEncryptionContext, SourceKeyId, DestinationKeyId, DestinationEncryptionContext, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm, GrantTokens);
    }
    public bool is_ReEncryptRequest { get { return true; } }
    public Dafny.ISequence<byte> dtor_CiphertextBlob {
      get {
        return this.CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SourceEncryptionContext {
      get {
        return this.SourceEncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId {
      get {
        return this.SourceKeyId;
      }
    }
    public Dafny.ISequence<char> dtor_DestinationKeyId {
      get {
        return this.DestinationKeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_DestinationEncryptionContext {
      get {
        return this.DestinationEncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm {
      get {
        return this.SourceEncryptionAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm {
      get {
        return this.DestinationEncryptionAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IReEncryptResponse {
    bool is_ReEncryptResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm { get; }
    _IReEncryptResponse DowncastClone();
  }
  public class ReEncryptResponse : _IReEncryptResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm;
    public ReEncryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm) {
      this.CiphertextBlob = CiphertextBlob;
      this.SourceKeyId = SourceKeyId;
      this.KeyId = KeyId;
      this.SourceEncryptionAlgorithm = SourceEncryptionAlgorithm;
      this.DestinationEncryptionAlgorithm = DestinationEncryptionAlgorithm;
    }
    public _IReEncryptResponse DowncastClone() {
      if (this is _IReEncryptResponse dt) { return dt; }
      return new ReEncryptResponse(CiphertextBlob, SourceKeyId, KeyId, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ReEncryptResponse;
      return oth != null && object.Equals(this.CiphertextBlob, oth.CiphertextBlob) && object.Equals(this.SourceKeyId, oth.SourceKeyId) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.SourceEncryptionAlgorithm, oth.SourceEncryptionAlgorithm) && object.Equals(this.DestinationEncryptionAlgorithm, oth.DestinationEncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SourceKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SourceEncryptionAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.DestinationEncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ReEncryptResponse.ReEncryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SourceKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SourceEncryptionAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.DestinationEncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _IReEncryptResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec>.Default());
    public static _IReEncryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReEncryptResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReEncryptResponse>(ComAmazonawsKmsTypes_Compile.ReEncryptResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReEncryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReEncryptResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm) {
      return new ReEncryptResponse(CiphertextBlob, SourceKeyId, KeyId, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm);
    }
    public bool is_ReEncryptResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this.CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId {
      get {
        return this.SourceKeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm {
      get {
        return this.SourceEncryptionAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm {
      get {
        return this.DestinationEncryptionAlgorithm;
      }
    }
  }

  public partial class RegionType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IReplicateKeyRequest {
    bool is_ReplicateKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_ReplicaRegion { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy { get; }
    Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_Tags { get; }
    _IReplicateKeyRequest DowncastClone();
  }
  public class ReplicateKeyRequest : _IReplicateKeyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<char> ReplicaRegion;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy;
    public readonly Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> Description;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags;
    public ReplicateKeyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> ReplicaRegion, Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags) {
      this.KeyId = KeyId;
      this.ReplicaRegion = ReplicaRegion;
      this.Policy = Policy;
      this.BypassPolicyLockoutSafetyCheck = BypassPolicyLockoutSafetyCheck;
      this.Description = Description;
      this.Tags = Tags;
    }
    public _IReplicateKeyRequest DowncastClone() {
      if (this is _IReplicateKeyRequest dt) { return dt; }
      return new ReplicateKeyRequest(KeyId, ReplicaRegion, Policy, BypassPolicyLockoutSafetyCheck, Description, Tags);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ReplicateKeyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.ReplicaRegion, oth.ReplicaRegion) && object.Equals(this.Policy, oth.Policy) && object.Equals(this.BypassPolicyLockoutSafetyCheck, oth.BypassPolicyLockoutSafetyCheck) && object.Equals(this.Description, oth.Description) && object.Equals(this.Tags, oth.Tags);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ReplicaRegion));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Policy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.BypassPolicyLockoutSafetyCheck));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Tags));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ReplicateKeyRequest.ReplicateKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ReplicaRegion);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Policy);
      s += ", ";
      s += Dafny.Helpers.ToString(this.BypassPolicyLockoutSafetyCheck);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Description);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Tags);
      s += ")";
      return s;
    }
    private static readonly _IReplicateKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>>.Default());
    public static _IReplicateKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReplicateKeyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReplicateKeyRequest>(ComAmazonawsKmsTypes_Compile.ReplicateKeyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReplicateKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReplicateKeyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> ReplicaRegion, Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> Tags) {
      return new ReplicateKeyRequest(KeyId, ReplicaRegion, Policy, BypassPolicyLockoutSafetyCheck, Description, Tags);
    }
    public bool is_ReplicateKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_ReplicaRegion {
      get {
        return this.ReplicaRegion;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy {
      get {
        return this.Policy;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck {
      get {
        return this.BypassPolicyLockoutSafetyCheck;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description {
      get {
        return this.Description;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_Tags {
      get {
        return this.Tags;
      }
    }
  }

  public interface _IReplicateKeyResponse {
    bool is_ReplicateKeyResponse { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> dtor_ReplicaKeyMetadata { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ReplicaPolicy { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_ReplicaTags { get; }
    _IReplicateKeyResponse DowncastClone();
  }
  public class ReplicateKeyResponse : _IReplicateKeyResponse {
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> ReplicaKeyMetadata;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> ReplicaPolicy;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> ReplicaTags;
    public ReplicateKeyResponse(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> ReplicaKeyMetadata, Wrappers_Compile._IOption<Dafny.ISequence<char>> ReplicaPolicy, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> ReplicaTags) {
      this.ReplicaKeyMetadata = ReplicaKeyMetadata;
      this.ReplicaPolicy = ReplicaPolicy;
      this.ReplicaTags = ReplicaTags;
    }
    public _IReplicateKeyResponse DowncastClone() {
      if (this is _IReplicateKeyResponse dt) { return dt; }
      return new ReplicateKeyResponse(ReplicaKeyMetadata, ReplicaPolicy, ReplicaTags);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ReplicateKeyResponse;
      return oth != null && object.Equals(this.ReplicaKeyMetadata, oth.ReplicaKeyMetadata) && object.Equals(this.ReplicaPolicy, oth.ReplicaPolicy) && object.Equals(this.ReplicaTags, oth.ReplicaTags);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ReplicaKeyMetadata));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ReplicaPolicy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ReplicaTags));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ReplicateKeyResponse.ReplicateKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.ReplicaKeyMetadata);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ReplicaPolicy);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ReplicaTags);
      s += ")";
      return s;
    }
    private static readonly _IReplicateKeyResponse theDefault = create(Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyMetadata>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>>.Default());
    public static _IReplicateKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReplicateKeyResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReplicateKeyResponse>(ComAmazonawsKmsTypes_Compile.ReplicateKeyResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IReplicateKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReplicateKeyResponse create(Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> ReplicaKeyMetadata, Wrappers_Compile._IOption<Dafny.ISequence<char>> ReplicaPolicy, Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> ReplicaTags) {
      return new ReplicateKeyResponse(ReplicaKeyMetadata, ReplicaPolicy, ReplicaTags);
    }
    public bool is_ReplicateKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyMetadata> dtor_ReplicaKeyMetadata {
      get {
        return this.ReplicaKeyMetadata;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ReplicaPolicy {
      get {
        return this.ReplicaPolicy;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag>> dtor_ReplicaTags {
      get {
        return this.ReplicaTags;
      }
    }
  }

  public interface _IRetireGrantRequest {
    bool is_RetireGrantRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    _IRetireGrantRequest DowncastClone();
  }
  public class RetireGrantRequest : _IRetireGrantRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId;
    public RetireGrantRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      this.GrantToken = GrantToken;
      this.KeyId = KeyId;
      this.GrantId = GrantId;
    }
    public _IRetireGrantRequest DowncastClone() {
      if (this is _IRetireGrantRequest dt) { return dt; }
      return new RetireGrantRequest(GrantToken, KeyId, GrantId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.RetireGrantRequest;
      return oth != null && object.Equals(this.GrantToken, oth.GrantToken) && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.GrantId, oth.GrantId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.RetireGrantRequest.RetireGrantRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.GrantToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantId);
      s += ")";
      return s;
    }
    private static readonly _IRetireGrantRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IRetireGrantRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IRetireGrantRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IRetireGrantRequest>(ComAmazonawsKmsTypes_Compile.RetireGrantRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IRetireGrantRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRetireGrantRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      return new RetireGrantRequest(GrantToken, KeyId, GrantId);
    }
    public bool is_RetireGrantRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken {
      get {
        return this.GrantToken;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this.GrantId;
      }
    }
  }

  public interface _IRevokeGrantRequest {
    bool is_RevokeGrantRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_GrantId { get; }
    _IRevokeGrantRequest DowncastClone();
  }
  public class RevokeGrantRequest : _IRevokeGrantRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<char> GrantId;
    public RevokeGrantRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GrantId) {
      this.KeyId = KeyId;
      this.GrantId = GrantId;
    }
    public _IRevokeGrantRequest DowncastClone() {
      if (this is _IRevokeGrantRequest dt) { return dt; }
      return new RevokeGrantRequest(KeyId, GrantId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.RevokeGrantRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.GrantId, oth.GrantId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.RevokeGrantRequest.RevokeGrantRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantId);
      s += ")";
      return s;
    }
    private static readonly _IRevokeGrantRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _IRevokeGrantRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IRevokeGrantRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IRevokeGrantRequest>(ComAmazonawsKmsTypes_Compile.RevokeGrantRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IRevokeGrantRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRevokeGrantRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GrantId) {
      return new RevokeGrantRequest(KeyId, GrantId);
    }
    public bool is_RevokeGrantRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_GrantId {
      get {
        return this.GrantId;
      }
    }
  }

  public interface _IScheduleKeyDeletionRequest {
    bool is_ScheduleKeyDeletionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_PendingWindowInDays { get; }
    _IScheduleKeyDeletionRequest DowncastClone();
  }
  public class ScheduleKeyDeletionRequest : _IScheduleKeyDeletionRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Wrappers_Compile._IOption<int> PendingWindowInDays;
    public ScheduleKeyDeletionRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      this.KeyId = KeyId;
      this.PendingWindowInDays = PendingWindowInDays;
    }
    public _IScheduleKeyDeletionRequest DowncastClone() {
      if (this is _IScheduleKeyDeletionRequest dt) { return dt; }
      return new ScheduleKeyDeletionRequest(KeyId, PendingWindowInDays);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ScheduleKeyDeletionRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.PendingWindowInDays, oth.PendingWindowInDays);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PendingWindowInDays));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ScheduleKeyDeletionRequest.ScheduleKeyDeletionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PendingWindowInDays);
      s += ")";
      return s;
    }
    private static readonly _IScheduleKeyDeletionRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<int>.Default());
    public static _IScheduleKeyDeletionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionRequest>(ComAmazonawsKmsTypes_Compile.ScheduleKeyDeletionRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IScheduleKeyDeletionRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      return new ScheduleKeyDeletionRequest(KeyId, PendingWindowInDays);
    }
    public bool is_ScheduleKeyDeletionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_PendingWindowInDays {
      get {
        return this.PendingWindowInDays;
      }
    }
  }

  public interface _IScheduleKeyDeletionResponse {
    bool is_ScheduleKeyDeletionResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> dtor_KeyState { get; }
    Wrappers_Compile._IOption<int> dtor_PendingWindowInDays { get; }
    _IScheduleKeyDeletionResponse DowncastClone();
  }
  public class ScheduleKeyDeletionResponse : _IScheduleKeyDeletionResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> KeyState;
    public readonly Wrappers_Compile._IOption<int> PendingWindowInDays;
    public ScheduleKeyDeletionResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> KeyState, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      this.KeyId = KeyId;
      this.DeletionDate = DeletionDate;
      this.KeyState = KeyState;
      this.PendingWindowInDays = PendingWindowInDays;
    }
    public _IScheduleKeyDeletionResponse DowncastClone() {
      if (this is _IScheduleKeyDeletionResponse dt) { return dt; }
      return new ScheduleKeyDeletionResponse(KeyId, DeletionDate, KeyState, PendingWindowInDays);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.ScheduleKeyDeletionResponse;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.DeletionDate, oth.DeletionDate) && object.Equals(this.KeyState, oth.KeyState) && object.Equals(this.PendingWindowInDays, oth.PendingWindowInDays);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.DeletionDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PendingWindowInDays));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.ScheduleKeyDeletionResponse.ScheduleKeyDeletionResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.DeletionDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyState);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PendingWindowInDays);
      s += ")";
      return s;
    }
    private static readonly _IScheduleKeyDeletionResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IKeyState>.Default(), Wrappers_Compile.Option<int>.Default());
    public static _IScheduleKeyDeletionResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionResponse>(ComAmazonawsKmsTypes_Compile.ScheduleKeyDeletionResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IScheduleKeyDeletionResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IScheduleKeyDeletionResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> KeyState, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      return new ScheduleKeyDeletionResponse(KeyId, DeletionDate, KeyState, PendingWindowInDays);
    }
    public bool is_ScheduleKeyDeletionResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate {
      get {
        return this.DeletionDate;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IKeyState> dtor_KeyState {
      get {
        return this.KeyState;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_PendingWindowInDays {
      get {
        return this.PendingWindowInDays;
      }
    }
  }

  public interface _ISigningAlgorithmSpec {
    bool is_RSASSA__PSS__SHA__256 { get; }
    bool is_RSASSA__PSS__SHA__384 { get; }
    bool is_RSASSA__PSS__SHA__512 { get; }
    bool is_RSASSA__PKCS1__V1__5__SHA__256 { get; }
    bool is_RSASSA__PKCS1__V1__5__SHA__384 { get; }
    bool is_RSASSA__PKCS1__V1__5__SHA__512 { get; }
    bool is_ECDSA__SHA__256 { get; }
    bool is_ECDSA__SHA__384 { get; }
    bool is_ECDSA__SHA__512 { get; }
    _ISigningAlgorithmSpec DowncastClone();
  }
  public abstract class SigningAlgorithmSpec : _ISigningAlgorithmSpec {
    public SigningAlgorithmSpec() { }
    private static readonly _ISigningAlgorithmSpec theDefault = create_RSASSA__PSS__SHA__256();
    public static _ISigningAlgorithmSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>(ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PSS__SHA__256() {
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__256();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PSS__SHA__384() {
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__384();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PSS__SHA__512() {
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__512();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PKCS1__V1__5__SHA__256() {
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PKCS1__V1__5__SHA__384() {
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PKCS1__V1__5__SHA__512() {
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512();
    }
    public static _ISigningAlgorithmSpec create_ECDSA__SHA__256() {
      return new SigningAlgorithmSpec_ECDSA__SHA__256();
    }
    public static _ISigningAlgorithmSpec create_ECDSA__SHA__384() {
      return new SigningAlgorithmSpec_ECDSA__SHA__384();
    }
    public static _ISigningAlgorithmSpec create_ECDSA__SHA__512() {
      return new SigningAlgorithmSpec_ECDSA__SHA__512();
    }
    public bool is_RSASSA__PSS__SHA__256 { get { return this is SigningAlgorithmSpec_RSASSA__PSS__SHA__256; } }
    public bool is_RSASSA__PSS__SHA__384 { get { return this is SigningAlgorithmSpec_RSASSA__PSS__SHA__384; } }
    public bool is_RSASSA__PSS__SHA__512 { get { return this is SigningAlgorithmSpec_RSASSA__PSS__SHA__512; } }
    public bool is_RSASSA__PKCS1__V1__5__SHA__256 { get { return this is SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256; } }
    public bool is_RSASSA__PKCS1__V1__5__SHA__384 { get { return this is SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384; } }
    public bool is_RSASSA__PKCS1__V1__5__SHA__512 { get { return this is SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512; } }
    public bool is_ECDSA__SHA__256 { get { return this is SigningAlgorithmSpec_ECDSA__SHA__256; } }
    public bool is_ECDSA__SHA__384 { get { return this is SigningAlgorithmSpec_ECDSA__SHA__384; } }
    public bool is_ECDSA__SHA__512 { get { return this is SigningAlgorithmSpec_ECDSA__SHA__512; } }
    public static System.Collections.Generic.IEnumerable<_ISigningAlgorithmSpec> AllSingletonConstructors {
      get {
        yield return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__256();
        yield return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__384();
        yield return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__512();
        yield return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__256();
        yield return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__384();
        yield return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__512();
        yield return SigningAlgorithmSpec.create_ECDSA__SHA__256();
        yield return SigningAlgorithmSpec.create_ECDSA__SHA__384();
        yield return SigningAlgorithmSpec.create_ECDSA__SHA__512();
      }
    }
    public abstract _ISigningAlgorithmSpec DowncastClone();
  }
  public class SigningAlgorithmSpec_RSASSA__PSS__SHA__256 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PSS__SHA__256() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_RSASSA__PSS__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.RSASSA_PSS_SHA_256";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PSS__SHA__384 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PSS__SHA__384() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_RSASSA__PSS__SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.RSASSA_PSS_SHA_384";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PSS__SHA__512 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PSS__SHA__512() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_RSASSA__PSS__SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.RSASSA_PSS_SHA_512";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512";
      return s;
    }
  }
  public class SigningAlgorithmSpec_ECDSA__SHA__256 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_ECDSA__SHA__256() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_ECDSA__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_ECDSA__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.ECDSA_SHA_256";
      return s;
    }
  }
  public class SigningAlgorithmSpec_ECDSA__SHA__384 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_ECDSA__SHA__384() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_ECDSA__SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_ECDSA__SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.ECDSA_SHA_384";
      return s;
    }
  }
  public class SigningAlgorithmSpec_ECDSA__SHA__512 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_ECDSA__SHA__512() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_ECDSA__SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec_ECDSA__SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.ECDSA_SHA_512";
      return s;
    }
  }

  public interface _ISignRequest {
    bool is_SignRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_Message { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> dtor_MessageType { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec dtor_SigningAlgorithm { get; }
    _ISignRequest DowncastClone();
  }
  public class SignRequest : _ISignRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<byte> Message;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> MessageType;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public readonly ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec SigningAlgorithm;
    public SignRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> MessageType, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec SigningAlgorithm) {
      this.KeyId = KeyId;
      this.Message = Message;
      this.MessageType = MessageType;
      this.GrantTokens = GrantTokens;
      this.SigningAlgorithm = SigningAlgorithm;
    }
    public _ISignRequest DowncastClone() {
      if (this is _ISignRequest dt) { return dt; }
      return new SignRequest(KeyId, Message, MessageType, GrantTokens, SigningAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SignRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Message, oth.Message) && object.Equals(this.MessageType, oth.MessageType) && object.Equals(this.GrantTokens, oth.GrantTokens) && object.Equals(this.SigningAlgorithm, oth.SigningAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Message));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.MessageType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SigningAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SignRequest.SignRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Message);
      s += ", ";
      s += Dafny.Helpers.ToString(this.MessageType);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SigningAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _ISignRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IMessageType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.Default());
    public static _ISignRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISignRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISignRequest>(ComAmazonawsKmsTypes_Compile.SignRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISignRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISignRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> MessageType, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec SigningAlgorithm) {
      return new SignRequest(KeyId, Message, MessageType, GrantTokens, SigningAlgorithm);
    }
    public bool is_SignRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_Message {
      get {
        return this.Message;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> dtor_MessageType {
      get {
        return this.MessageType;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
    public ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec dtor_SigningAlgorithm {
      get {
        return this.SigningAlgorithm;
      }
    }
  }

  public interface _ISignResponse {
    bool is_SignResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Signature { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> dtor_SigningAlgorithm { get; }
    _ISignResponse DowncastClone();
  }
  public class SignResponse : _ISignResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> Signature;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> SigningAlgorithm;
    public SignResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Signature, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> SigningAlgorithm) {
      this.KeyId = KeyId;
      this.Signature = Signature;
      this.SigningAlgorithm = SigningAlgorithm;
    }
    public _ISignResponse DowncastClone() {
      if (this is _ISignResponse dt) { return dt; }
      return new SignResponse(KeyId, Signature, SigningAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.SignResponse;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Signature, oth.Signature) && object.Equals(this.SigningAlgorithm, oth.SigningAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Signature));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SigningAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.SignResponse.SignResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Signature);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SigningAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _ISignResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>.Default());
    public static _ISignResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISignResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISignResponse>(ComAmazonawsKmsTypes_Compile.SignResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ISignResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISignResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Signature, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> SigningAlgorithm) {
      return new SignResponse(KeyId, Signature, SigningAlgorithm);
    }
    public bool is_SignResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Signature {
      get {
        return this.Signature;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> dtor_SigningAlgorithm {
      get {
        return this.SigningAlgorithm;
      }
    }
  }

  public interface _ITag {
    bool is_Tag { get; }
    Dafny.ISequence<char> dtor_TagKey { get; }
    Dafny.ISequence<char> dtor_TagValue { get; }
    _ITag DowncastClone();
  }
  public class Tag : _ITag {
    public readonly Dafny.ISequence<char> TagKey;
    public readonly Dafny.ISequence<char> TagValue;
    public Tag(Dafny.ISequence<char> TagKey, Dafny.ISequence<char> TagValue) {
      this.TagKey = TagKey;
      this.TagValue = TagValue;
    }
    public _ITag DowncastClone() {
      if (this is _ITag dt) { return dt; }
      return new Tag(TagKey, TagValue);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Tag;
      return oth != null && object.Equals(this.TagKey, oth.TagKey) && object.Equals(this.TagValue, oth.TagValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TagKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TagValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Tag.Tag";
      s += "(";
      s += Dafny.Helpers.ToString(this.TagKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.TagValue);
      s += ")";
      return s;
    }
    private static readonly _ITag theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _ITag Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ITag> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ITag>(ComAmazonawsKmsTypes_Compile.Tag.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ITag> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITag create(Dafny.ISequence<char> TagKey, Dafny.ISequence<char> TagValue) {
      return new Tag(TagKey, TagValue);
    }
    public bool is_Tag { get { return true; } }
    public Dafny.ISequence<char> dtor_TagKey {
      get {
        return this.TagKey;
      }
    }
    public Dafny.ISequence<char> dtor_TagValue {
      get {
        return this.TagValue;
      }
    }
  }

  public partial class TagKeyType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITagResourceRequest {
    bool is_TagResourceRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag> dtor_Tags { get; }
    _ITagResourceRequest DowncastClone();
  }
  public class TagResourceRequest : _ITagResourceRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag> Tags;
    public TagResourceRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag> Tags) {
      this.KeyId = KeyId;
      this.Tags = Tags;
    }
    public _ITagResourceRequest DowncastClone() {
      if (this is _ITagResourceRequest dt) { return dt; }
      return new TagResourceRequest(KeyId, Tags);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.TagResourceRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Tags, oth.Tags);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Tags));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.TagResourceRequest.TagResourceRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Tags);
      s += ")";
      return s;
    }
    private static readonly _ITagResourceRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<ComAmazonawsKmsTypes_Compile._ITag>.Empty);
    public static _ITagResourceRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ITagResourceRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ITagResourceRequest>(ComAmazonawsKmsTypes_Compile.TagResourceRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._ITagResourceRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITagResourceRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag> Tags) {
      return new TagResourceRequest(KeyId, Tags);
    }
    public bool is_TagResourceRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<ComAmazonawsKmsTypes_Compile._ITag> dtor_Tags {
      get {
        return this.Tags;
      }
    }
  }

  public partial class TagValueType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class TrustAnchorCertificateType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IUntagResourceRequest {
    bool is_UntagResourceRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<Dafny.ISequence<char>> dtor_TagKeys { get; }
    _IUntagResourceRequest DowncastClone();
  }
  public class UntagResourceRequest : _IUntagResourceRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<Dafny.ISequence<char>> TagKeys;
    public UntagResourceRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<Dafny.ISequence<char>> TagKeys) {
      this.KeyId = KeyId;
      this.TagKeys = TagKeys;
    }
    public _IUntagResourceRequest DowncastClone() {
      if (this is _IUntagResourceRequest dt) { return dt; }
      return new UntagResourceRequest(KeyId, TagKeys);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.UntagResourceRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.TagKeys, oth.TagKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TagKeys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.UntagResourceRequest.UntagResourceRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.TagKeys);
      s += ")";
      return s;
    }
    private static readonly _IUntagResourceRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<Dafny.ISequence<char>>.Empty);
    public static _IUntagResourceRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUntagResourceRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUntagResourceRequest>(ComAmazonawsKmsTypes_Compile.UntagResourceRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUntagResourceRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUntagResourceRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<Dafny.ISequence<char>> TagKeys) {
      return new UntagResourceRequest(KeyId, TagKeys);
    }
    public bool is_UntagResourceRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<char>> dtor_TagKeys {
      get {
        return this.TagKeys;
      }
    }
  }

  public interface _IUpdateAliasRequest {
    bool is_UpdateAliasRequest { get; }
    Dafny.ISequence<char> dtor_AliasName { get; }
    Dafny.ISequence<char> dtor_TargetKeyId { get; }
    _IUpdateAliasRequest DowncastClone();
  }
  public class UpdateAliasRequest : _IUpdateAliasRequest {
    public readonly Dafny.ISequence<char> AliasName;
    public readonly Dafny.ISequence<char> TargetKeyId;
    public UpdateAliasRequest(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      this.AliasName = AliasName;
      this.TargetKeyId = TargetKeyId;
    }
    public _IUpdateAliasRequest DowncastClone() {
      if (this is _IUpdateAliasRequest dt) { return dt; }
      return new UpdateAliasRequest(AliasName, TargetKeyId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.UpdateAliasRequest;
      return oth != null && object.Equals(this.AliasName, oth.AliasName) && object.Equals(this.TargetKeyId, oth.TargetKeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.AliasName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.TargetKeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.UpdateAliasRequest.UpdateAliasRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.AliasName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.TargetKeyId);
      s += ")";
      return s;
    }
    private static readonly _IUpdateAliasRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _IUpdateAliasRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateAliasRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateAliasRequest>(ComAmazonawsKmsTypes_Compile.UpdateAliasRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateAliasRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateAliasRequest create(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      return new UpdateAliasRequest(AliasName, TargetKeyId);
    }
    public bool is_UpdateAliasRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_AliasName {
      get {
        return this.AliasName;
      }
    }
    public Dafny.ISequence<char> dtor_TargetKeyId {
      get {
        return this.TargetKeyId;
      }
    }
  }

  public interface _IUpdateCustomKeyStoreRequest {
    bool is_UpdateCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NewCustomKeyStoreName { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyStorePassword { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId { get; }
    _IUpdateCustomKeyStoreRequest DowncastClone();
  }
  public class UpdateCustomKeyStoreRequest : _IUpdateCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> NewCustomKeyStoreName;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyStorePassword;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId;
    public UpdateCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> NewCustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyStorePassword, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId) {
      this.CustomKeyStoreId = CustomKeyStoreId;
      this.NewCustomKeyStoreName = NewCustomKeyStoreName;
      this.KeyStorePassword = KeyStorePassword;
      this.CloudHsmClusterId = CloudHsmClusterId;
    }
    public _IUpdateCustomKeyStoreRequest DowncastClone() {
      if (this is _IUpdateCustomKeyStoreRequest dt) { return dt; }
      return new UpdateCustomKeyStoreRequest(CustomKeyStoreId, NewCustomKeyStoreName, KeyStorePassword, CloudHsmClusterId);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.UpdateCustomKeyStoreRequest;
      return oth != null && object.Equals(this.CustomKeyStoreId, oth.CustomKeyStoreId) && object.Equals(this.NewCustomKeyStoreName, oth.NewCustomKeyStoreName) && object.Equals(this.KeyStorePassword, oth.KeyStorePassword) && object.Equals(this.CloudHsmClusterId, oth.CloudHsmClusterId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.NewCustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyStorePassword));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.CloudHsmClusterId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.UpdateCustomKeyStoreRequest.UpdateCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.NewCustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.KeyStorePassword);
      s += ", ";
      s += Dafny.Helpers.ToString(this.CloudHsmClusterId);
      s += ")";
      return s;
    }
    private static readonly _IUpdateCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IUpdateCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreRequest>(ComAmazonawsKmsTypes_Compile.UpdateCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> NewCustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyStorePassword, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId) {
      return new UpdateCustomKeyStoreRequest(CustomKeyStoreId, NewCustomKeyStoreName, KeyStorePassword, CloudHsmClusterId);
    }
    public bool is_UpdateCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this.CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NewCustomKeyStoreName {
      get {
        return this.NewCustomKeyStoreName;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyStorePassword {
      get {
        return this.KeyStorePassword;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId {
      get {
        return this.CloudHsmClusterId;
      }
    }
  }

  public interface _IUpdateCustomKeyStoreResponse {
    bool is_UpdateCustomKeyStoreResponse { get; }
    _IUpdateCustomKeyStoreResponse DowncastClone();
  }
  public class UpdateCustomKeyStoreResponse : _IUpdateCustomKeyStoreResponse {
    public UpdateCustomKeyStoreResponse() {
    }
    public _IUpdateCustomKeyStoreResponse DowncastClone() {
      if (this is _IUpdateCustomKeyStoreResponse dt) { return dt; }
      return new UpdateCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.UpdateCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.UpdateCustomKeyStoreResponse.UpdateCustomKeyStoreResponse";
      return s;
    }
    private static readonly _IUpdateCustomKeyStoreResponse theDefault = create();
    public static _IUpdateCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreResponse>(ComAmazonawsKmsTypes_Compile.UpdateCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateCustomKeyStoreResponse create() {
      return new UpdateCustomKeyStoreResponse();
    }
    public bool is_UpdateCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IUpdateCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return UpdateCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IUpdateKeyDescriptionRequest {
    bool is_UpdateKeyDescriptionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_Description { get; }
    _IUpdateKeyDescriptionRequest DowncastClone();
  }
  public class UpdateKeyDescriptionRequest : _IUpdateKeyDescriptionRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<char> Description;
    public UpdateKeyDescriptionRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> Description) {
      this.KeyId = KeyId;
      this.Description = Description;
    }
    public _IUpdateKeyDescriptionRequest DowncastClone() {
      if (this is _IUpdateKeyDescriptionRequest dt) { return dt; }
      return new UpdateKeyDescriptionRequest(KeyId, Description);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.UpdateKeyDescriptionRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Description, oth.Description);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Description));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.UpdateKeyDescriptionRequest.UpdateKeyDescriptionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Description);
      s += ")";
      return s;
    }
    private static readonly _IUpdateKeyDescriptionRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _IUpdateKeyDescriptionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateKeyDescriptionRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateKeyDescriptionRequest>(ComAmazonawsKmsTypes_Compile.UpdateKeyDescriptionRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdateKeyDescriptionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateKeyDescriptionRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> Description) {
      return new UpdateKeyDescriptionRequest(KeyId, Description);
    }
    public bool is_UpdateKeyDescriptionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_Description {
      get {
        return this.Description;
      }
    }
  }

  public interface _IUpdatePrimaryRegionRequest {
    bool is_UpdatePrimaryRegionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_PrimaryRegion { get; }
    _IUpdatePrimaryRegionRequest DowncastClone();
  }
  public class UpdatePrimaryRegionRequest : _IUpdatePrimaryRegionRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<char> PrimaryRegion;
    public UpdatePrimaryRegionRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PrimaryRegion) {
      this.KeyId = KeyId;
      this.PrimaryRegion = PrimaryRegion;
    }
    public _IUpdatePrimaryRegionRequest DowncastClone() {
      if (this is _IUpdatePrimaryRegionRequest dt) { return dt; }
      return new UpdatePrimaryRegionRequest(KeyId, PrimaryRegion);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.UpdatePrimaryRegionRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.PrimaryRegion, oth.PrimaryRegion);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.PrimaryRegion));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.UpdatePrimaryRegionRequest.UpdatePrimaryRegionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.PrimaryRegion);
      s += ")";
      return s;
    }
    private static readonly _IUpdatePrimaryRegionRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static _IUpdatePrimaryRegionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdatePrimaryRegionRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdatePrimaryRegionRequest>(ComAmazonawsKmsTypes_Compile.UpdatePrimaryRegionRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IUpdatePrimaryRegionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdatePrimaryRegionRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PrimaryRegion) {
      return new UpdatePrimaryRegionRequest(KeyId, PrimaryRegion);
    }
    public bool is_UpdatePrimaryRegionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_PrimaryRegion {
      get {
        return this.PrimaryRegion;
      }
    }
  }

  public interface _IVerifyRequest {
    bool is_VerifyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_Message { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> dtor_MessageType { get; }
    Dafny.ISequence<byte> dtor_Signature { get; }
    ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec dtor_SigningAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IVerifyRequest DowncastClone();
  }
  public class VerifyRequest : _IVerifyRequest {
    public readonly Dafny.ISequence<char> KeyId;
    public readonly Dafny.ISequence<byte> Message;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> MessageType;
    public readonly Dafny.ISequence<byte> Signature;
    public readonly ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec SigningAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens;
    public VerifyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> MessageType, Dafny.ISequence<byte> Signature, ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec SigningAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this.KeyId = KeyId;
      this.Message = Message;
      this.MessageType = MessageType;
      this.Signature = Signature;
      this.SigningAlgorithm = SigningAlgorithm;
      this.GrantTokens = GrantTokens;
    }
    public _IVerifyRequest DowncastClone() {
      if (this is _IVerifyRequest dt) { return dt; }
      return new VerifyRequest(KeyId, Message, MessageType, Signature, SigningAlgorithm, GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.VerifyRequest;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.Message, oth.Message) && object.Equals(this.MessageType, oth.MessageType) && object.Equals(this.Signature, oth.Signature) && object.Equals(this.SigningAlgorithm, oth.SigningAlgorithm) && object.Equals(this.GrantTokens, oth.GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Message));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.MessageType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Signature));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SigningAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.VerifyRequest.VerifyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Message);
      s += ", ";
      s += Dafny.Helpers.ToString(this.MessageType);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Signature);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SigningAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.GrantTokens);
      s += ")";
      return s;
    }
    private static readonly _IVerifyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._IMessageType>.Default(), Dafny.Sequence<byte>.Empty, ComAmazonawsKmsTypes_Compile.SigningAlgorithmSpec.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static _IVerifyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IVerifyRequest> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IVerifyRequest>(ComAmazonawsKmsTypes_Compile.VerifyRequest.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IVerifyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVerifyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> MessageType, Dafny.ISequence<byte> Signature, ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec SigningAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new VerifyRequest(KeyId, Message, MessageType, Signature, SigningAlgorithm, GrantTokens);
    }
    public bool is_VerifyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_Message {
      get {
        return this.Message;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._IMessageType> dtor_MessageType {
      get {
        return this.MessageType;
      }
    }
    public Dafny.ISequence<byte> dtor_Signature {
      get {
        return this.Signature;
      }
    }
    public ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec dtor_SigningAlgorithm {
      get {
        return this.SigningAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this.GrantTokens;
      }
    }
  }

  public interface _IVerifyResponse {
    bool is_VerifyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<bool> dtor_SignatureValid { get; }
    Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> dtor_SigningAlgorithm { get; }
    _IVerifyResponse DowncastClone();
  }
  public class VerifyResponse : _IVerifyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId;
    public readonly Wrappers_Compile._IOption<bool> SignatureValid;
    public readonly Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> SigningAlgorithm;
    public VerifyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<bool> SignatureValid, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> SigningAlgorithm) {
      this.KeyId = KeyId;
      this.SignatureValid = SignatureValid;
      this.SigningAlgorithm = SigningAlgorithm;
    }
    public _IVerifyResponse DowncastClone() {
      if (this is _IVerifyResponse dt) { return dt; }
      return new VerifyResponse(KeyId, SignatureValid, SigningAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.VerifyResponse;
      return oth != null && object.Equals(this.KeyId, oth.KeyId) && object.Equals(this.SignatureValid, oth.SignatureValid) && object.Equals(this.SigningAlgorithm, oth.SigningAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SignatureValid));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.SigningAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.VerifyResponse.VerifyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SignatureValid);
      s += ", ";
      s += Dafny.Helpers.ToString(this.SigningAlgorithm);
      s += ")";
      return s;
    }
    private static readonly _IVerifyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec>.Default());
    public static _IVerifyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IVerifyResponse> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IVerifyResponse>(ComAmazonawsKmsTypes_Compile.VerifyResponse.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IVerifyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVerifyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<bool> SignatureValid, Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> SigningAlgorithm) {
      return new VerifyResponse(KeyId, SignatureValid, SigningAlgorithm);
    }
    public bool is_VerifyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this.KeyId;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_SignatureValid {
      get {
        return this.SignatureValid;
      }
    }
    public Wrappers_Compile._IOption<ComAmazonawsKmsTypes_Compile._ISigningAlgorithmSpec> dtor_SigningAlgorithm {
      get {
        return this.SigningAlgorithm;
      }
    }
  }

  public interface _IWrappingKeySpec {
    bool is_RSA__2048 { get; }
    _IWrappingKeySpec DowncastClone();
  }
  public class WrappingKeySpec : _IWrappingKeySpec {
    public WrappingKeySpec() {
    }
    public _IWrappingKeySpec DowncastClone() {
      if (this is _IWrappingKeySpec dt) { return dt; }
      return new WrappingKeySpec();
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.WrappingKeySpec;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.WrappingKeySpec.RSA_2048";
      return s;
    }
    private static readonly _IWrappingKeySpec theDefault = create();
    public static _IWrappingKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IWrappingKeySpec> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IWrappingKeySpec>(ComAmazonawsKmsTypes_Compile.WrappingKeySpec.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IWrappingKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWrappingKeySpec create() {
      return new WrappingKeySpec();
    }
    public bool is_RSA__2048 { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IWrappingKeySpec> AllSingletonConstructors {
      get {
        yield return WrappingKeySpec.create();
      }
    }
  }

  public interface _IError {
    bool is_CloudHsmClusterNotFoundException { get; }
    bool is_CustomKeyStoreHasCMKsException { get; }
    bool is_TagException { get; }
    bool is_InvalidImportTokenException { get; }
    bool is_CloudHsmClusterNotRelatedException { get; }
    bool is_DependencyTimeoutException { get; }
    bool is_InvalidGrantIdException { get; }
    bool is_MalformedPolicyDocumentException { get; }
    bool is_ExpiredImportTokenException { get; }
    bool is_UnsupportedOperationException { get; }
    bool is_InvalidGrantTokenException { get; }
    bool is_KeyUnavailableException { get; }
    bool is_KMSInternalException { get; }
    bool is_IncorrectKeyMaterialException { get; }
    bool is_InvalidCiphertextException { get; }
    bool is_IncorrectTrustAnchorException { get; }
    bool is_InvalidMarkerException { get; }
    bool is_LimitExceededException { get; }
    bool is_InvalidKeyUsageException { get; }
    bool is_AlreadyExistsException { get; }
    bool is_InvalidArnException { get; }
    bool is_CustomKeyStoreNotFoundException { get; }
    bool is_InvalidAliasNameException { get; }
    bool is_CloudHsmClusterInUseException { get; }
    bool is_CloudHsmClusterInvalidConfigurationException { get; }
    bool is_CustomKeyStoreNameInUseException { get; }
    bool is_KMSInvalidSignatureException { get; }
    bool is_KMSInvalidStateException { get; }
    bool is_IncorrectKeyException { get; }
    bool is_CloudHsmClusterNotActiveException { get; }
    bool is_CustomKeyStoreInvalidStateException { get; }
    bool is_DisabledException { get; }
    bool is_NotFoundException { get; }
    bool is_Opaque { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_message { get; }
    object dtor_obj { get; }
    _IError DowncastClone();
  }
  public abstract class Error : _IError {
    public Error() { }
    private static readonly _IError theDefault = create_CloudHsmClusterNotFoundException(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static _IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IError> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IError>(ComAmazonawsKmsTypes_Compile.Error.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create_CloudHsmClusterNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterNotFoundException(message);
    }
    public static _IError create_CustomKeyStoreHasCMKsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreHasCMKsException(message);
    }
    public static _IError create_TagException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_TagException(message);
    }
    public static _IError create_InvalidImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidImportTokenException(message);
    }
    public static _IError create_CloudHsmClusterNotRelatedException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterNotRelatedException(message);
    }
    public static _IError create_DependencyTimeoutException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_DependencyTimeoutException(message);
    }
    public static _IError create_InvalidGrantIdException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidGrantIdException(message);
    }
    public static _IError create_MalformedPolicyDocumentException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_MalformedPolicyDocumentException(message);
    }
    public static _IError create_ExpiredImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_ExpiredImportTokenException(message);
    }
    public static _IError create_UnsupportedOperationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_UnsupportedOperationException(message);
    }
    public static _IError create_InvalidGrantTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidGrantTokenException(message);
    }
    public static _IError create_KeyUnavailableException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KeyUnavailableException(message);
    }
    public static _IError create_KMSInternalException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KMSInternalException(message);
    }
    public static _IError create_IncorrectKeyMaterialException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_IncorrectKeyMaterialException(message);
    }
    public static _IError create_InvalidCiphertextException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidCiphertextException(message);
    }
    public static _IError create_IncorrectTrustAnchorException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_IncorrectTrustAnchorException(message);
    }
    public static _IError create_InvalidMarkerException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidMarkerException(message);
    }
    public static _IError create_LimitExceededException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_LimitExceededException(message);
    }
    public static _IError create_InvalidKeyUsageException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidKeyUsageException(message);
    }
    public static _IError create_AlreadyExistsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_AlreadyExistsException(message);
    }
    public static _IError create_InvalidArnException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidArnException(message);
    }
    public static _IError create_CustomKeyStoreNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreNotFoundException(message);
    }
    public static _IError create_InvalidAliasNameException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidAliasNameException(message);
    }
    public static _IError create_CloudHsmClusterInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterInUseException(message);
    }
    public static _IError create_CloudHsmClusterInvalidConfigurationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterInvalidConfigurationException(message);
    }
    public static _IError create_CustomKeyStoreNameInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreNameInUseException(message);
    }
    public static _IError create_KMSInvalidSignatureException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KMSInvalidSignatureException(message);
    }
    public static _IError create_KMSInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KMSInvalidStateException(message);
    }
    public static _IError create_IncorrectKeyException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_IncorrectKeyException(message);
    }
    public static _IError create_CloudHsmClusterNotActiveException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterNotActiveException(message);
    }
    public static _IError create_CustomKeyStoreInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreInvalidStateException(message);
    }
    public static _IError create_DisabledException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_DisabledException(message);
    }
    public static _IError create_NotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_NotFoundException(message);
    }
    public static _IError create_Opaque(object obj) {
      return new Error_Opaque(obj);
    }
    public bool is_CloudHsmClusterNotFoundException { get { return this is Error_CloudHsmClusterNotFoundException; } }
    public bool is_CustomKeyStoreHasCMKsException { get { return this is Error_CustomKeyStoreHasCMKsException; } }
    public bool is_TagException { get { return this is Error_TagException; } }
    public bool is_InvalidImportTokenException { get { return this is Error_InvalidImportTokenException; } }
    public bool is_CloudHsmClusterNotRelatedException { get { return this is Error_CloudHsmClusterNotRelatedException; } }
    public bool is_DependencyTimeoutException { get { return this is Error_DependencyTimeoutException; } }
    public bool is_InvalidGrantIdException { get { return this is Error_InvalidGrantIdException; } }
    public bool is_MalformedPolicyDocumentException { get { return this is Error_MalformedPolicyDocumentException; } }
    public bool is_ExpiredImportTokenException { get { return this is Error_ExpiredImportTokenException; } }
    public bool is_UnsupportedOperationException { get { return this is Error_UnsupportedOperationException; } }
    public bool is_InvalidGrantTokenException { get { return this is Error_InvalidGrantTokenException; } }
    public bool is_KeyUnavailableException { get { return this is Error_KeyUnavailableException; } }
    public bool is_KMSInternalException { get { return this is Error_KMSInternalException; } }
    public bool is_IncorrectKeyMaterialException { get { return this is Error_IncorrectKeyMaterialException; } }
    public bool is_InvalidCiphertextException { get { return this is Error_InvalidCiphertextException; } }
    public bool is_IncorrectTrustAnchorException { get { return this is Error_IncorrectTrustAnchorException; } }
    public bool is_InvalidMarkerException { get { return this is Error_InvalidMarkerException; } }
    public bool is_LimitExceededException { get { return this is Error_LimitExceededException; } }
    public bool is_InvalidKeyUsageException { get { return this is Error_InvalidKeyUsageException; } }
    public bool is_AlreadyExistsException { get { return this is Error_AlreadyExistsException; } }
    public bool is_InvalidArnException { get { return this is Error_InvalidArnException; } }
    public bool is_CustomKeyStoreNotFoundException { get { return this is Error_CustomKeyStoreNotFoundException; } }
    public bool is_InvalidAliasNameException { get { return this is Error_InvalidAliasNameException; } }
    public bool is_CloudHsmClusterInUseException { get { return this is Error_CloudHsmClusterInUseException; } }
    public bool is_CloudHsmClusterInvalidConfigurationException { get { return this is Error_CloudHsmClusterInvalidConfigurationException; } }
    public bool is_CustomKeyStoreNameInUseException { get { return this is Error_CustomKeyStoreNameInUseException; } }
    public bool is_KMSInvalidSignatureException { get { return this is Error_KMSInvalidSignatureException; } }
    public bool is_KMSInvalidStateException { get { return this is Error_KMSInvalidStateException; } }
    public bool is_IncorrectKeyException { get { return this is Error_IncorrectKeyException; } }
    public bool is_CloudHsmClusterNotActiveException { get { return this is Error_CloudHsmClusterNotActiveException; } }
    public bool is_CustomKeyStoreInvalidStateException { get { return this is Error_CustomKeyStoreInvalidStateException; } }
    public bool is_DisabledException { get { return this is Error_DisabledException; } }
    public bool is_NotFoundException { get { return this is Error_NotFoundException; } }
    public bool is_Opaque { get { return this is Error_Opaque; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_message {
      get {
        var d = this;
        if (d is Error_CloudHsmClusterNotFoundException) { return ((Error_CloudHsmClusterNotFoundException)d).message; }
        if (d is Error_CustomKeyStoreHasCMKsException) { return ((Error_CustomKeyStoreHasCMKsException)d).message; }
        if (d is Error_TagException) { return ((Error_TagException)d).message; }
        if (d is Error_InvalidImportTokenException) { return ((Error_InvalidImportTokenException)d).message; }
        if (d is Error_CloudHsmClusterNotRelatedException) { return ((Error_CloudHsmClusterNotRelatedException)d).message; }
        if (d is Error_DependencyTimeoutException) { return ((Error_DependencyTimeoutException)d).message; }
        if (d is Error_InvalidGrantIdException) { return ((Error_InvalidGrantIdException)d).message; }
        if (d is Error_MalformedPolicyDocumentException) { return ((Error_MalformedPolicyDocumentException)d).message; }
        if (d is Error_ExpiredImportTokenException) { return ((Error_ExpiredImportTokenException)d).message; }
        if (d is Error_UnsupportedOperationException) { return ((Error_UnsupportedOperationException)d).message; }
        if (d is Error_InvalidGrantTokenException) { return ((Error_InvalidGrantTokenException)d).message; }
        if (d is Error_KeyUnavailableException) { return ((Error_KeyUnavailableException)d).message; }
        if (d is Error_KMSInternalException) { return ((Error_KMSInternalException)d).message; }
        if (d is Error_IncorrectKeyMaterialException) { return ((Error_IncorrectKeyMaterialException)d).message; }
        if (d is Error_InvalidCiphertextException) { return ((Error_InvalidCiphertextException)d).message; }
        if (d is Error_IncorrectTrustAnchorException) { return ((Error_IncorrectTrustAnchorException)d).message; }
        if (d is Error_InvalidMarkerException) { return ((Error_InvalidMarkerException)d).message; }
        if (d is Error_LimitExceededException) { return ((Error_LimitExceededException)d).message; }
        if (d is Error_InvalidKeyUsageException) { return ((Error_InvalidKeyUsageException)d).message; }
        if (d is Error_AlreadyExistsException) { return ((Error_AlreadyExistsException)d).message; }
        if (d is Error_InvalidArnException) { return ((Error_InvalidArnException)d).message; }
        if (d is Error_CustomKeyStoreNotFoundException) { return ((Error_CustomKeyStoreNotFoundException)d).message; }
        if (d is Error_InvalidAliasNameException) { return ((Error_InvalidAliasNameException)d).message; }
        if (d is Error_CloudHsmClusterInUseException) { return ((Error_CloudHsmClusterInUseException)d).message; }
        if (d is Error_CloudHsmClusterInvalidConfigurationException) { return ((Error_CloudHsmClusterInvalidConfigurationException)d).message; }
        if (d is Error_CustomKeyStoreNameInUseException) { return ((Error_CustomKeyStoreNameInUseException)d).message; }
        if (d is Error_KMSInvalidSignatureException) { return ((Error_KMSInvalidSignatureException)d).message; }
        if (d is Error_KMSInvalidStateException) { return ((Error_KMSInvalidStateException)d).message; }
        if (d is Error_IncorrectKeyException) { return ((Error_IncorrectKeyException)d).message; }
        if (d is Error_CloudHsmClusterNotActiveException) { return ((Error_CloudHsmClusterNotActiveException)d).message; }
        if (d is Error_CustomKeyStoreInvalidStateException) { return ((Error_CustomKeyStoreInvalidStateException)d).message; }
        if (d is Error_DisabledException) { return ((Error_DisabledException)d).message; }
        return ((Error_NotFoundException)d).message;
      }
    }
    public object dtor_obj {
      get {
        var d = this;
        return ((Error_Opaque)d).obj;
      }
    }
    public abstract _IError DowncastClone();
  }
  public class Error_CloudHsmClusterNotFoundException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CloudHsmClusterNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterNotFoundException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CloudHsmClusterNotFoundException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CloudHsmClusterNotFoundException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreHasCMKsException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CustomKeyStoreHasCMKsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreHasCMKsException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CustomKeyStoreHasCMKsException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CustomKeyStoreHasCMKsException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_TagException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_TagException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_TagException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_TagException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.TagException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidImportTokenException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidImportTokenException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidImportTokenException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidImportTokenException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterNotRelatedException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CloudHsmClusterNotRelatedException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterNotRelatedException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CloudHsmClusterNotRelatedException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CloudHsmClusterNotRelatedException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_DependencyTimeoutException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_DependencyTimeoutException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_DependencyTimeoutException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_DependencyTimeoutException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.DependencyTimeoutException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidGrantIdException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidGrantIdException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidGrantIdException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidGrantIdException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidGrantIdException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_MalformedPolicyDocumentException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_MalformedPolicyDocumentException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_MalformedPolicyDocumentException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_MalformedPolicyDocumentException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.MalformedPolicyDocumentException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_ExpiredImportTokenException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_ExpiredImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_ExpiredImportTokenException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_ExpiredImportTokenException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.ExpiredImportTokenException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_UnsupportedOperationException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_UnsupportedOperationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_UnsupportedOperationException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_UnsupportedOperationException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.UnsupportedOperationException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidGrantTokenException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidGrantTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidGrantTokenException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidGrantTokenException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidGrantTokenException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_KeyUnavailableException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_KeyUnavailableException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KeyUnavailableException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_KeyUnavailableException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.KeyUnavailableException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_KMSInternalException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_KMSInternalException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KMSInternalException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_KMSInternalException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.KMSInternalException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_IncorrectKeyMaterialException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_IncorrectKeyMaterialException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_IncorrectKeyMaterialException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_IncorrectKeyMaterialException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.IncorrectKeyMaterialException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidCiphertextException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidCiphertextException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidCiphertextException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidCiphertextException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidCiphertextException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_IncorrectTrustAnchorException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_IncorrectTrustAnchorException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_IncorrectTrustAnchorException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_IncorrectTrustAnchorException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.IncorrectTrustAnchorException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidMarkerException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidMarkerException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidMarkerException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidMarkerException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidMarkerException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_LimitExceededException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_LimitExceededException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_LimitExceededException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_LimitExceededException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.LimitExceededException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidKeyUsageException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidKeyUsageException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidKeyUsageException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidKeyUsageException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidKeyUsageException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_AlreadyExistsException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_AlreadyExistsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_AlreadyExistsException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_AlreadyExistsException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.AlreadyExistsException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidArnException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidArnException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidArnException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidArnException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidArnException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreNotFoundException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CustomKeyStoreNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreNotFoundException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CustomKeyStoreNotFoundException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CustomKeyStoreNotFoundException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidAliasNameException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_InvalidAliasNameException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidAliasNameException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_InvalidAliasNameException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.InvalidAliasNameException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterInUseException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CloudHsmClusterInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterInUseException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CloudHsmClusterInUseException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CloudHsmClusterInUseException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterInvalidConfigurationException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CloudHsmClusterInvalidConfigurationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterInvalidConfigurationException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CloudHsmClusterInvalidConfigurationException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CloudHsmClusterInvalidConfigurationException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreNameInUseException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CustomKeyStoreNameInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreNameInUseException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CustomKeyStoreNameInUseException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CustomKeyStoreNameInUseException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_KMSInvalidSignatureException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_KMSInvalidSignatureException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KMSInvalidSignatureException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_KMSInvalidSignatureException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.KMSInvalidSignatureException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_KMSInvalidStateException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_KMSInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KMSInvalidStateException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_KMSInvalidStateException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 27;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.KMSInvalidStateException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_IncorrectKeyException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_IncorrectKeyException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_IncorrectKeyException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_IncorrectKeyException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.IncorrectKeyException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterNotActiveException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CloudHsmClusterNotActiveException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterNotActiveException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CloudHsmClusterNotActiveException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 29;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CloudHsmClusterNotActiveException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreInvalidStateException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_CustomKeyStoreInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreInvalidStateException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_CustomKeyStoreInvalidStateException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.CustomKeyStoreInvalidStateException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_DisabledException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_DisabledException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_DisabledException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_DisabledException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 31;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.DisabledException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_NotFoundException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> message;
    public Error_NotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_NotFoundException(message);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_NotFoundException;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 32;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.NotFoundException";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_Opaque : Error {
    public readonly object obj;
    public Error_Opaque(object obj) {
      this.obj = obj;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_Opaque(obj);
    }
    public override bool Equals(object other) {
      var oth = other as ComAmazonawsKmsTypes_Compile.Error_Opaque;
      return oth != null && this.obj == oth.obj;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 33;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ComAmazonawsKmsTypes_Compile.Error.Opaque";
      s += "(";
      s += Dafny.Helpers.ToString(this.obj);
      s += ")";
      return s;
    }
  }

  public partial class OpaqueError {
    private static readonly Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IError> _TYPE = new Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IError>(ComAmazonawsKmsTypes_Compile.Error.Default());
    public static Dafny.TypeDescriptor<ComAmazonawsKmsTypes_Compile._IError> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsValid__AliasNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__ArnType(Dafny.ISequence<char> x) {
      return ((new BigInteger(20)) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(2048)));
    }
    public static bool IsValid__CiphertextType(Dafny.ISequence<byte> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(6144)));
    }
    public static bool IsValid__CloudHsmClusterIdType(Dafny.ISequence<char> x) {
      return ((new BigInteger(19)) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(24)));
    }
    public static bool IsValid__CustomKeyStoreIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(64)));
    }
    public static bool IsValid__CustomKeyStoreNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__DescriptionType(Dafny.ISequence<char> x) {
      return ((new BigInteger((x).Count)).Sign != -1) && ((new BigInteger((x).Count)) <= (new BigInteger(8192)));
    }
    public static bool IsValid__GrantIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(128)));
    }
    public static bool IsValid__GrantNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__GrantTokenList(Dafny.ISequence<Dafny.ISequence<char>> x) {
      return ((new BigInteger((x).Count)).Sign != -1) && ((new BigInteger((x).Count)) <= (new BigInteger(10)));
    }
    public static bool IsValid__GrantTokenType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(8192)));
    }
    public static bool IsValid__KeyIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(2048)));
    }
    public static bool IsValid__KeyStorePasswordType(Dafny.ISequence<char> x) {
      return ((new BigInteger(7)) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(32)));
    }
    public static bool IsValid__LimitType(int x) {
      return ((1) <= (x)) && ((x) <= (1000));
    }
    public static bool IsValid__MarkerType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(1024)));
    }
    public static bool IsValid__NumberOfBytesType(int x) {
      return ((1) <= (x)) && ((x) <= (1024));
    }
    public static bool IsValid__PendingWindowInDaysType(int x) {
      return ((1) <= (x)) && ((x) <= (365));
    }
    public static bool IsValid__PlaintextType(Dafny.ISequence<byte> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(4096)));
    }
    public static bool IsValid__PolicyNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(128)));
    }
    public static bool IsValid__PolicyType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(131072)));
    }
    public static bool IsValid__PrincipalIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__PublicKeyType(Dafny.ISequence<byte> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(8192)));
    }
    public static bool IsValid__RegionType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(32)));
    }
    public static bool IsValid__TagKeyType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(128)));
    }
    public static bool IsValid__TagValueType(Dafny.ISequence<char> x) {
      return ((new BigInteger((x).Count)).Sign != -1) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__TrustAnchorCertificateType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(5000)));
    }
  }
} // end of namespace ComAmazonawsKmsTypes_Compile
namespace Com_mAmazonaws_mKms_Compile {

  public partial class __default {
    public static Com_mAmazonaws_mKms_Compile._IKMSClientConfigType DefaultKMSClientConfigType() {
      return Com_mAmazonaws_mKms_Compile.KMSClientConfigType.create();
    }
  }

  public interface _IKMSClientConfigType {
    bool is_KMSClientConfigType { get; }
    _IKMSClientConfigType DowncastClone();
  }
  public class KMSClientConfigType : _IKMSClientConfigType {
    public KMSClientConfigType() {
    }
    public _IKMSClientConfigType DowncastClone() {
      if (this is _IKMSClientConfigType dt) { return dt; }
      return new KMSClientConfigType();
    }
    public override bool Equals(object other) {
      var oth = other as Com_mAmazonaws_mKms_Compile.KMSClientConfigType;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Com_mAmazonaws_mKms_Compile.KMSClientConfigType.KMSClientConfigType";
      return s;
    }
    private static readonly _IKMSClientConfigType theDefault = create();
    public static _IKMSClientConfigType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Com_mAmazonaws_mKms_Compile._IKMSClientConfigType> _TYPE = new Dafny.TypeDescriptor<Com_mAmazonaws_mKms_Compile._IKMSClientConfigType>(Com_mAmazonaws_mKms_Compile.KMSClientConfigType.Default());
    public static Dafny.TypeDescriptor<Com_mAmazonaws_mKms_Compile._IKMSClientConfigType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKMSClientConfigType create() {
      return new KMSClientConfigType();
    }
    public bool is_KMSClientConfigType { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IKMSClientConfigType> AllSingletonConstructors {
      get {
        yield return KMSClientConfigType.create();
      }
    }
  }
} // end of namespace Com_mAmazonaws_mKms_Compile
namespace Com_mAmazonaws_Compile {

} // end of namespace Com_mAmazonaws_Compile
namespace Com_Compile {

} // end of namespace Com_Compile
namespace _module {

} // end of namespace _module
