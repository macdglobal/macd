// SPDX-License-Identifier：MIT
语用固结度^ 0。6。0 ;
编译实验ABIEncoderV2;

导入 “ ./Utils.sol”；
导入 “ ./InnerProductVerifier.sol”；

合同BurnVerifier {
    将Utils 用于uint256;
     为Utils.G1Point使用Utils；

    InnerProductVerifier ip;

    结构BurnStatement {
        Utils.G1Point CLn;
        Utils.G1Point CRn;
        Utils.G1Point y;
        uint256时代; //还是uint8？
        地址发件人；
        Utils.G1Point u;
    }

    struct BurnProof {
        Utils.G1Point BA;
        Utils.G1Point BS;

        Utils.G1Point [ 2 ] tCommits;
        uint256 tHat;
        uint256亩;

        uint256 c;
        uint256 s_sk;
        uint256 s_b;
        uint256 s_tau;

        InnerProductVerifier.InnerProductProof ipProof;
    }

    构造函数（地址 _ip）公共{
        ip =  InnerProductVerifier（_ip）;
    }

    函数verifyBurn（Utils.G1Point存储器CLn，Utils.G1Point存储器CRn，Utils.G1Point存储器y，uint256 纪元，Utils.G1Point存储器u，地址 发送者，字节 存储 证明）公共 视图 返回（bool）{
        BurnStatement内存语句；//警告：如果直接在控制台中调用，
        //并且您的字符串少于64个字符，将在右侧而不是左侧进行填充。希望不会成为问题，
        //，因为通常其他合同会简单地调用它。不过，要当心
        statement.CLn = CLn;
        statement.CRn = CRn的;
        statement.y = ÿ;
        statement.epoch =纪元;
        statement.u = u;
        statement.sender =发送者；
        BurnProof内存burnProof =反 序列化（证明）；
        返回 验证（声明，burnProof）；
    }

    struct BurnAuxiliaries {
        uint256 y;
        uint256 [ 32 ] ys;
        uint256 z;
        uint256 [ 1 ] zs; //很傻。只是为了匹配zether。
        uint256 zSum;
        uint256 [ 32 ] twoTimesZSquared;
        uint256 x;
        uint256 t;
        uint256 k;
        Utils.G1Point tEval;
    }

    SigmaAuxiliaries结构{
        uint256 c;
        Utils.G1Point A_y;
        Utils.G1Point A_b;
        Utils.G1Point A_t;
        Utils.G1Point gEpoch;
        Utils.G1Point A_u;
    }

    struct IPAuxiliaries {
        Utils.G1Point P;
        Utils.G1Point u_x;
        Utils.G1Point [] hPrimes;
        Utils.G1Point hPrimeSum;
        uint256 o;
    }

    函数gSum（）内部 纯 返回值（Utils.G1Point内存）{
        返回实用程序。G1Point（0x2257118d30fe5064dda298b2fac15cf96fd51f0e7e3df342d0aed40b8d7bb151，0x0d4250e7509c99370e6b15ebfe4f1aa5e65a691133357901aa4b0641f96c80a8）;
    }

    函数验证（BurnStatement内存语句，BurnProof内存证明）内部 视图 返回（bool）{
        uint256 statementHash = uint256（keccak256（ABI。编码（statement.CLn，statement.CRn，statement.y，statement.epoch，statement.sender）））。gMod（）; // stacktoodeep？

        BurnAuxiliaries内存burnAuxiliaries；
        burnAuxiliaries.y =  uint256（keccak256（ABI。编码（statementHash，proof.BA，proof.BS）））。gMod（）;
        burnAuxiliaries.ys [ 0 ] =  1 ;
        burnAuxiliaries.k =  1 ;
        对于（uint256 i = 1 ; i <  32 ; i ++）{
            burnAuxiliaries.ys [i] = burnAuxiliaries.ys [i -  1 ]。gMul（burnAuxiliaries.y）;
            burnAuxiliaries.k = burnAuxiliaries.k。gAdd（burnAuxiliaries.ys [i]）;
        }
        burnAuxiliaries.z =  uint256（keccak256（abi。编码（burnAuxiliaries.y）））。gMod（）;
        burnAuxiliaries.zs = [burnAuxiliaries.z。gExp（2）];
        burnAuxiliaries.zSum = burnAuxiliaries.zs [ 0 ]。gMul（burnAuxiliaries.z）; //微不足道的总和
        burnAuxiliaries.k = burnAuxiliaries.k。gMul（burnAuxiliaries.z。GSUB（burnAuxiliaries.zs [ 0 ]））。GSUB（burnAuxiliaries.zSum。gMul（2  **  32）。GSUB（burnAuxiliaries.zSum））;
        burnAuxiliaries.t = proof.tHat。gSub（burnAuxiliaries.k）;
        对于（uint256 i = 0 ; i <  32 ; i ++）{
            burnAuxiliaries.twoTimesZSquared [i] = burnAuxiliaries.zs [ 0 ]。gMul（2  ** i）;
        }

        burnAuxiliaries.x =  uint256（keccak256（abi。编码（burnAuxiliaries.z，proof.tCommits）））。gMod（）;
        burnAuxiliaries.tEval = proof.tCommits [ 0 ]。pMul（burnAuxiliaries.x）。pAdd（proof.tCommits [ 1 ] 。pMul（burnAuxiliaries.x。gMul（burnAuxiliaries.x）））; //替换为“提交”吗？

        SigmaAuxiliaries内存sigmaAuxiliaries;
        sigmaAuxiliaries.A_y =实用程序。g（）。pMul（proof.s_sk）。PADD（statement.y PMUL（proof.c。gNeg（）））;
        sigmaAuxiliaries.A_b =实用程序。g（）。pMul（proof.s_b）。PADD（statement.CRn。PMUL（proof.s_sk）。PADD（statement.CLn。PMUL（proof.c。gNeg（）））。PMUL（burnAuxiliaries.zs [ 0 ]））;
        sigmaAuxiliaries.A_t =实用程序。g（）。pMul（burnAuxiliaries.t）。PADD（burnAuxiliaries.tEval。pNeg（））。pMul（proof.c）。pAdd（实用程序h（）。pMul（proof.s_tau））。pAdd（实用g（）。pMul（proof.s_b。gNeg（）））;
        sigmaAuxiliaries.gEpoch =实用程序。mapInto（“ Suter”，statement.epoch）;
        sigmaAuxiliaries.A_u = sigmaAuxiliaries.gEpoch。pMul（proof.s_sk）。PADD（statement.u PMUL（proof.c。gNeg（）））;

        sigmaAuxiliaries.c =  uint256（keccak256（abi。编码（burnAuxiliaries.x，sigmaAuxiliaries.A_y，sigmaAuxiliaries.A_b，sigmaAuxiliaries.A_t，sigmaAuxiliaries.A_u）））。gMod（）;
        要求（sigmaAuxiliaries.c == proof.c，串（ABI。encodePacked（“西格玛协议挑战平等失败”。，utils的。uint2str（statement.epoch））））;

        IPAuxiliaries内存ipAuxiliaries；
        ipAuxiliaries.o =  uint256（keccak256（ABI。编码（sigmaAuxiliaries.c）））。gMod（）;
        ipAuxiliaries.u_x =实用程序。g（）。pMul（ipAuxiliaries.o）；
        ipAuxiliaries.hPrimes = 新的实用程序。G1Point []（32）;
        对于（uint256 i = 0 ; i <  32 ; i ++）{
            ipAuxiliaries.hPrimes [i] = ip。hs（i）。pMul（burnAuxiliaries.ys [i] 。gInv（））；
            ipAuxiliaries.hPrimeSum = ipAuxiliaries.hPrimeSum。pAdd（ipAuxiliaries.hPrimes [i] 。pMul（burnAuxiliaries.ys [i] 。gMul（burnAuxiliaries.z）。gAdd（burnAuxiliaries.twoTimesZSquared [i]）））;
        }
        ipAuxiliaries.P =证明BA。PADD（proof.BS。PMUL（burnAuxiliaries.x））。pAdd（gSum（）。pMul（burnAuxiliaries.z。gNeg（）））。pAdd（ipAuxiliaries.hPrimeSum）;
        ipAuxiliaries.P = ipAuxiliaries.P。PADD（utils的。ħ（）。PMUL（proof.mu。gNeg（）））;
        ipAuxiliaries.P = ipAuxiliaries.P。PADD（ipAuxiliaries.u_x PMUL（proof.tHat））;
        要求（ip.verifyInnerProduct（ipAuxiliaries.hPrimes，ipAuxiliaries.u_x，ipAuxiliaries.P，proof.ipProof，ipAuxiliaries.o），“内部产品证明验证失败。”）；

        返回 true ;
    }

    函数反序列化（字节 内存 arr）内部 纯 返回值（BurnProof内存证明）{
        proof.BA =实用程序。G1Point（utils的。切片（ARR，0），utils的。切片（ARR，32））;
        proof.BS =实用程序。G1Point（utils的。切片（ARR，64），utils的。切片（ARR，96））;

        proof.tCommits = [实用程序。G1Point（实用程序切片（arr，128），实用程序切片（arr，160）），实用程序 G1Point（utils的。切片（ARR，192），utils的。切片（ARR，224））];
        proof.tHat =  uint256（实用程序切片（arr，256））;
        proof.mu =  uint256（实用程序切片（arr，288））;

        proof.c =  uint256（实用程序切片（arr，320））;
        proof.s_sk =  uint256（实用程序切片（arr，352））;
        proof.s_b =  uint256（实用程序切片（arr，384））;
        proof.s_tau =  uint256（实用程序切片（arr，416））;

        InnerProductVerifier.InnerProductProof内存ipProof;
        ipProof.ls = 新的实用程序。G1Point []（5）;
        ipProof.rs = 新的实用程序。G1Point []（5）;
        for（uint256 i = 0 ; i <  5 ; i ++）{ // 2 ^ 5 = 32。
            ipProof.ls [i] =实用程序。G1Point（utils的。切片（ARR，448  +我*  64），utils的。切片（ARR，480  +我*  64））;
            ipProof.rs [i] =实用程序。G1Point（utils的切片（ARR，448  +（5  + I）*  64），utils的。切片（ARR，480  +（5  + I）*  64））;
        }
        ipProof.a =  uint256（实用程序切片（arr，448  +  5  *  128））;
        ipProof.b =  uint256（实用程序切片（arr，480  +  5  *  128））;
        proof.ipProof = ipProof;

        退货证明;
    }
}
