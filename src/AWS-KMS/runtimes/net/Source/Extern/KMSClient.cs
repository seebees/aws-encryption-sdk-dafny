using Amazon.KeyManagementService;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Kms;

// This extern is identified in Dafny code
// that refines the AWS SDK KMS Model
namespace Dafny.Com.Amazonaws.Kms
{
    public partial class __default
    {
        public static
            _IResult<
                Types.IKeyManagementServiceClient,
                Types._IError
            >
            KMSClient()
        {
            var client = new AmazonKeyManagementServiceClient();

            return Result<
                Types.IKeyManagementServiceClient,
                Types._IError
            >
                .create_Success(new KeyManagementServiceShim(client));
        }
    }
}
