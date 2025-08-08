# mpc

This is a repository for Neo X ZK-DKG MPC ceremony, please refer [bane-labs/zk-dkg](https://github.com/bane-labs/zk-dkg) about the tool and [neo-x-mpc](https://github.com/bane-labs/zk-dkg/blob/main/neo-x-mpc.md) about the steps.

## Information

|Name              |Property                                    |
|------------------|--------------------------------------------|
|Proof System      |Groth16                                     |
|Power of Tau      |2^24                                        |
|Number of Circuits|3                                           |
|NeoFS Network     |Mainnet                                     |
|NeoFS Container   |411d8vuzogogMxXJqTQcu61btgQ6rL2VNYUYnH7r4kE3|

NGD is responsible for phase initialization and sealing, so we expect the contribution order to be **NGD=>NSPCC=>AxLabs=>lazynode**.

## How to Contribute

Please contribute the MPC file according to the order, upload the result through NeoFS, and provide following information through **pull request**:

1. Result file challenge, you can get it from the `zk-dkg` command line output after computation;
2. NeoFS object ID, you can get it from the `neofs-cli` command line output after file upload.

After all of the MPC contributions, NGD will backup the results to cloud, so please leave the `Cloud URL` field as empty in pull requests.

## Phase1 Attestations

|Participant|File Challenge                                                  |NeoFS Object ID                             |Cloud URL|
|-----------|----------------------------------------------------------------|--------------------------------------------|---------|
|NGD        |071d2176b99861f97e57020cd5ef3904299fffb1fdb8bf0994d9bbf5e36f60ad|4t51oBmnwu3UHpC35HAS3aoF2jcMtjmpL9df7vZR447r|         |
|NSPCC      |                                                                |                                            |         |
|AxLabs     |                                                                |                                            |         |
|lazynode   |                                                                |                                            |         |

The beacon challenge for sealing: 

## Phase2 Attestations

### Circuit 1 (1-Message)

|Participant|File Challenge|NeoFS Object ID|Cloud URL|
|-----------|--------------|---------------|---------|
|NGD        |              |               |         |
|NSPCC      |              |               |         |
|AxLabs     |              |               |         |
|lazynode   |              |               |         |

The beacon challenge for sealing: 

### Circuit 2 (2-Message)

|Participant|File Challenge|NeoFS Object ID|Cloud URL|
|-----------|--------------|---------------|---------|
|NGD        |              |               |         |
|NSPCC      |              |               |         |
|AxLabs     |              |               |         |
|lazynode   |              |               |         |

The beacon challenge for sealing: 

### Circuit 3 (7-Message)

|Participant|File Challenge|NeoFS Object ID|Cloud URL|
|-----------|--------------|---------------|---------|
|NGD        |              |               |         |
|NSPCC      |              |               |         |
|AxLabs     |              |               |         |
|lazynode   |              |               |         |

The beacon challenge for sealing: 
