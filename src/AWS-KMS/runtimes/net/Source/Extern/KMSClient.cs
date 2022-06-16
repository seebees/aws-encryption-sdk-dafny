using Amazon.KeyManagementService;
using Wrappers_Compile;
using Amazon.Runtime;

namespace Dafny.Com.Amazonaws.Kms
{
    public partial class __default
    {
        public static
            _IResult<
                Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient,
                Dafny.Com.Amazonaws.Kms.Types._IError
            >
            KMSClient()
        {
            var asdf = new EnvironmentVariablesAWSCredentials();
            var client = new AmazonKeyManagementServiceClient(
                asdf
                );

            return Result<
                Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient,
                Dafny.Com.Amazonaws.Kms.Types._IError>
                .create_Success(new Kms.KeyManagementServiceShim(client));
        }
    }
}
