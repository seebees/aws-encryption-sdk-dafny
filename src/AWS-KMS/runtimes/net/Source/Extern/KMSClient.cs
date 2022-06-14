using Amazon;
using Amazon.KeyManagementService;
using Amazon.Runtime;

namespace Com.Amazonaws.Kms
{
  public partial class __default {

    public static 
      Wrappers_Compile._IResult<
        Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
        Dafny.Com.Amazonaws.Kms.Error
      >
    KMSClient() {
      client = new AmazonKeyManagementServiceClient();

      return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
        Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Success(
        AWS.EncryptionSDK.Core.TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(client)
      );
     }
  }

}
