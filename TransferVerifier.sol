// SPDX-License-Identifier：MIT
语用固结度^ 0。6。0 ;
编译实验ABIEncoderV2;

导入 “ ./Utils.sol”；
导入 “ ./InnerProductVerifier.sol”；

合同TransferVerifier {
    将Utils 用于uint256;
     为Utils.G1Point使用Utils；

    uint256 常数UNITY = 0x14a3074b02521e3b1ed9852e5028452693e87be4e910500c7ba9bbddb2f46edd ; //基元2 ^ 28的整数模q的根。

    InnerProductVerifier ip;

    struct TransferStatement {
        Utils.G1Point [] CLn;
        Utils.G1Point [] CRn;
        Utils.G1Point [] C;
        Utils.G1Point D;
        Utils.G1Point [] y;
        uint256时代;
        Utils.G1Point u;
    }

    struct TransferProof {
        Utils.G1Point BA;
        Utils.G1Point BS;
        实用程序G1点A;
        实用程序G1点B;

        Utils.G1Point [] CLnG;
        Utils.G1Point [] CRnG;
        Utils.G1Point [] C_0G;
        Utils.G1Point [] DG;
        Utils.G1Point [] y_0G;
        Utils.G1Point [] gG;
        Utils.G1Point [] C_XG;
        Utils.G1Point [] y_XG;

        uint256 [] f;
        uint256 z_A;
        uint256 z_C;
        uint256 z_E;

        Utils.G1Point [ 2 ] tCommits;
        uint256 tHat;
        uint256亩;

        uint256 c;
        uint256 s_sk;
        uint256 s_r;
        uint256 s_b;
        uint256 s_tau;

        InnerProductVerifier.InnerProductProof ipProof;
    }

    构造函数（地址 _ip）公共{
        ip =  InnerProductVerifier（_ip）;
    }

    函数verifyTransfer（Utils.G1Point []内存CLn，Utils.G1Point []内存CRn，Utils.G1Point []内存C，Utils.G1Point内存D，Utils.G1Point []内存y，uint256 历元，Utils.G1Point内存u字节 内存 证明）公共 视图 返回（bool）{
        TransferStatement内存语句；
        statement.CLn = CLn; //我需要分配/设置大小吗？
        statement.CRn = CRn的;
        statement.C = C。;
        statement.D = d;
        statement.y = ÿ;
        statement.epoch =纪元;
        statement.u = u;
        TransferProof内存zetherProof =反 序列化（证明）；
        返回 验证（语句，zetherProof）；
    }

    struct TransferAuxiliaries {
        uint256 y;
        uint256 [ 64 ] ys;
        uint256 z;
        uint256 [ 2 ] zs; // [z ^ 2，z ^ 3]
        uint256 [ 64 ] twoTimesZSquared;
        uint256 zSum;
        uint256 x;
        uint256 t;
        uint256 k;
        Utils.G1Point tEval;
    }

    SigmaAuxiliaries结构{
        uint256 c;
        Utils.G1Point A_y;
        Utils.G1Point A_D;
        Utils.G1Point A_b;
        Utils.G1Point A_X;
        Utils.G1Point A_t;
        Utils.G1Point gEpoch;
        Utils.G1Point A_u;
    }

    struct AnonAuxiliaries {
        uint256 m;
        uint256 N;
        uint256 v;
        uint256 w;
        uint256 vPow;
        uint256 wPow;
        uint256 [ 2 ] [] f; //可以只在证明中分配额外的空间吗？
        uint256 [ 2 ] [] r; //每个poly是长度为N的数组。
        Utils.G1Point temp;
        Utils.G1Point CLnR;
        Utils.G1Point CRnR;
        Utils.G1Point [ 2 ] [] CR;
        Utils.G1Point [ 2 ] [] yR;
        Utils.G1Point C_XR;
        Utils.G1Point y_XR;
        Utils.G1Point gR;
        Utils.G1Point DR;
    }

    struct IPAuxiliaries {
        Utils.G1Point P;
        Utils.G1Point u_x;
        Utils.G1Point [] hPrimes;
        Utils.G1Point hPrimeSum;
        uint256 o;
    }

    函数gSum（）内部 纯 返回值（Utils.G1Point内存）{
        返回实用程序。G1Point（0x00715f13ea08d6b51bedcde3599d8e12163e090921309d5aafc9b5bfaadbcda0，0x27aceab598af7bf3d16ca9d40fe186c489382c21bb9d22b19cb3af8b751b959f）;
    }

    函数验证（TransferStatement内存语句，TransferProof内存证明）内部 视图 返回（bool）{
        uint256 statementHash = uint256（keccak256（abi。编码（statement.CLn，statement.CRn，statement.C，statement.D，statement.y，statement.epoch）））。gMod（）;

        AnonAuxiliaries内存anonAuxiliaries;
        anonAuxiliaries.v =  uint256（keccak256（abi。编码（statementHash，proof.BA，proof.BS，proof.A，proof.B）））。gMod（）;
        anonAuxiliaries.w =  uint256（keccak256（abi。编码（anonAuxiliaries.v，proof.CLnG，proof.CRnG，proof.C_0G，proof.DG，proof.y_0G，proof.gG，proof.C_XG，proof.y_XG））） 。gMod（）;
        anonAuxiliaries.m =证明f。长度 /  2 ;
        N =  2  ** anonAuxiliaries.m;
        anonAuxiliaries.f = 新的 uint256 [ 2 ] []（2  * anonAuxiliaries.m）;
        for（uint256 k = 0 ; k <  2  * anonAuxiliaries.m; k ++）{
            anonAuxiliaries.f [k] [ 1 ] = proof.f [k];
            anonAuxiliaries.f [k] [ 0 ] = anonAuxiliaries.w。gSub（proof.f [k]）;
        }

        for（uint256 k = 0 ; k <  2  * anonAuxiliaries.m; k ++）{
            anonAuxiliaries.temp = anonAuxiliaries.temp。PADD（IP。GS（K）。PMUL（anonAuxiliaries.f [k]的[ 1 ]））;
            anonAuxiliaries.temp = anonAuxiliaries.temp。PADD（IP GS（K +  2  * anonAuxiliaries.m）。PMUL（anonAuxiliaries.f [k]的[ 1 ]。gMul（anonAuxiliaries.w。GSUB（anonAuxiliaries.f [k]的[ 1 ]））））;
        }
        anonAuxiliaries.temp = anonAuxiliaries.temp。PADD（IP。GS（4  * anonAuxiliaries.m）。PMUL（anonAuxiliaries.f [ 0 ] [ 1 ]。gMul（anonAuxiliaries.f [anonAuxiliaries.m] [ 1 ]））。PADD（IP。GS（1  +  4  * anonAuxiliaries.m）。pMul（anonAuxiliaries.f [ 0 ] [ 0 ] 。gMul（anonAuxiliaries.f [anonAuxiliaries.m] [ 0 ]））））;
        要求（proof.B。PMUL（anonAuxiliaries.w）。PADD（proof.A）。pEqual（anonAuxiliaries.temp。PADD（utils的。ħ（）。PMUL（proof.z_A））），“恢复对于B ^ W失败* A.“）;

        anonAuxiliaries.r = 组装多项式（anonAuxiliaries.f）;

        anonAuxiliaries.CR =  assembleConvolutions（anonAuxiliaries.r，statement.C）;
        anonAuxiliaries.y =  assembleConvolutions（anonAuxiliaries.r，statement.y）;
        对于（uint256 i = 0 ; i < anonAuxiliaries.N; i ++）{
            anonAuxiliaries.CLnR = anonAuxiliaries.CLnR。pAdd（statement.CLn [i] 。pMul（anonAuxiliaries.r [i] [ 0 ]））;
            anonAuxiliaries.CRnR = anonAuxiliaries.CRnR。pAdd（statement.CRn [i] 。pMul（anonAuxiliaries.r [i] [ 0 ]））;
        }
        anonAuxiliaries.vPow =  1 ;
        对于（uint256 i = 0 ; i < anonAuxiliaries.N; i ++）{
            anonAuxiliaries.C_XR = anonAuxiliaries.C_XR。pAdd（anonAuxiliaries.CR [i /  2 ] [i ％ 2 ] 。pMul（anonAuxiliaries.vPow））;
            anonAuxiliaries.y_XR = anonAuxiliaries.y_XR。pAdd（anonAuxiliaries.yR [i /  2 ] [i ％ 2 ] 。pMul（anonAuxiliaries.vPow））;
            如果（i >  0）{
                anonAuxiliaries.vPow = anonAuxiliaries.vPow。gMul（anonAuxiliaries.v）;
            }
        }
        anonAuxiliaries.wPow =  1 ;
        for（uint256 k = 0 ; k < anonAuxiliaries.m; k ++）{
            anonAuxiliaries.CLnR = anonAuxiliaries.CLnR。pAdd（proof.CLnG [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））；
            anonAuxiliaries.CRnR = anonAuxiliaries.CRnR。pAdd（proof.CRnG [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））；
            anonAuxiliaries.CR [ 0 ] [ 0 ] = anonAuxiliaries.CR [ 0 ] [ 0 ]。pAdd（proof.C_0G [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））；
            anonAuxiliaries.DR = anonAuxiliaries.DR。pAdd（proof.DG [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））;
            anonAuxiliaries.yR [ 0 ] [ 0 ] = anonAuxiliaries.yR [ 0 ] [ 0 ]。pAdd（proof.y_0G [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））;
            anonAuxiliaries.gR = anonAuxiliaries.gR。pAdd（proof.gG [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））;
            anonAuxiliaries.C_XR = anonAuxiliaries.C_XR。pAdd（proof.C_XG [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））；
            anonAuxiliaries.y_XR = anonAuxiliaries.y_XR。pAdd（proof.y_XG [k] 。pMul（anonAuxiliaries.wPow。gNeg（）））；

            anonAuxiliaries.wPow = anonAuxiliaries.wPow。gMul（anonAuxiliaries.w）;
        }
        anonAuxiliaries.DR = anonAuxiliaries.DR。PADD（statement.D PMUL（anonAuxiliaries.wPow））;
        anonAuxiliaries.gR = anonAuxiliaries.gR。pAdd（实用g（）。pMul（anonAuxiliaries.wPow））;

        TransferAuxiliaries内存zetherAuxiliaries;
        zetherAuxiliaries.y =  uint256（keccak256（ABI。编码（anonAuxiliaries.w）））。gMod（）;
        zetherAuxiliaries.ys [ 0 ] =  1 ;
        zetherAuxiliaries.k =  1 ;
        对于（uint256 i = 1 ; i <  64 ; i ++）{
            zetherAuxiliaries.ys [i] = zetherAuxiliaries.ys [i -  1 ]。gMul（zetherAuxiliaries.y）;
            zetherAuxiliaries.k = zetherAuxiliaries.k。gAdd（zetherAuxiliaries.ys [i]）;
        }
        zetherAuxiliaries.z =  uint256（keccak256（abi。编码（zetherAuxiliaries.y）））。gMod（）;
        zetherAuxiliaries.zs = [zetherAuxiliaries.z。gExp（2），zetherAuxiliaries.z。gExp（3）];        
        zetherAuxiliaries.zSum = zetherAuxiliaries.zs [ 0 ]。gAdd（zetherAuxiliaries.zs [ 1 ]）。gMul（zetherAuxiliaries.z）;
        zetherAuxiliaries.k = zetherAuxiliaries.k。gMul（zetherAuxiliaries.z。GSUB（zetherAuxiliaries.zs [ 0 ]））。GSUB（zetherAuxiliaries.zSum。gMul（2  **  32）。GSUB（zetherAuxiliaries.zSum））;
        zetherAuxiliaries.t = proof.tHat。gSub（zetherAuxiliaries.k）; // t = tHat-delta（y，z）
        对于（uint256 i = 0 ; i <  32 ; i ++）{
            zetherAuxiliaries.twoTimesZSquared [i] = zetherAuxiliaries.zs [ 0 ]。gMul（2  ** i）;
            zetherAuxiliaries.twoTimesZSquared [i +  32 ] = zetherAuxiliaries.zs [ 1 ]。gMul（2  ** i）;
        }

        zetherAuxiliaries.x =  uint256（keccak256（abi。编码（zetherAuxiliaries.z，proof.tCommits）））。gMod（）;
        zetherAuxiliaries.tEval = proof.tCommits [ 0 ]。pMul（zetherAuxiliaries.x）。pAdd（proof.tCommits [ 1 ] 。pMul（zetherAuxiliaries.x。gMul（zetherAuxiliaries.x）））; //替换为“提交”吗？

        SigmaAuxiliaries内存sigmaAuxiliaries;
        sigmaAuxiliaries.A_y = anonAuxiliaries.gR。pMul（proof.s_sk）。pAdd（anonAuxiliaries.yR [ 0 ] [ 0 ] 。pMul（proof.c。gNeg（）））;
        sigmaAuxiliaries.A_D =实用程序。g（）。pMul（proof.s_r）。PADD（statement.D。PMUL（proof.c。gNeg（）））; //添加（mul（anonAuxiliaries.gR，proof.s_r），mul（anonAuxiliaries.DR，proof.c.neg（）））;
        sigmaAuxiliaries.A_b =实用程序。g（）。pMul（proof.s_b）。PADD（anonAuxiliaries.DR。PMUL（zetherAuxiliaries.zs [ 0 ]。gNeg（））。PADD（anonAuxiliaries.CRnR。PMUL（zetherAuxiliaries.zs [ 1 ]））。PMUL（proof.s_sk）。PADD（anonAuxiliaries.CR [ 0 ] [ 0 ] 。pMul（zetherAuxiliaries.zs [ 0 ] 。gNeg（））。pAdd（anonAuxiliaries.CLnR。pMul（zetherAuxiliaries.zs [ 1 ]））。PMUL（proof.c。gNeg（））））;
        sigmaAuxiliaries.A_X = anonAuxiliaries.y_XR。pMul（proof.s_r）。PADD（anonAuxiliaries.C_XR。PMUL（proof.c。gNeg（）））;
        sigmaAuxiliaries.A_t =实用程序。g（）。pMul（zetherAuxiliaries.t）。PADD（zetherAuxiliaries.tEval。pNeg（））。PMUL（proof.c。gMul（anonAuxiliaries.wPow））。pAdd（实用程序h（）。pMul（proof.s_tau））。pAdd（实用g（）。pMul（proof.s_b。gNeg（）））;
        sigmaAuxiliaries.gEpoch =实用程序。mapInto（“ Suter”，statement.epoch）;
        sigmaAuxiliaries.A_u = sigmaAuxiliaries.gEpoch。pMul（proof.s_sk）。PADD（statement.u PMUL（proof.c。gNeg（）））;

        sigmaAuxiliaries.c =  uint256（keccak256（abi。编码（zetherAuxiliaries.x，sigmaAuxiliaries.A_y，sigmaAuxiliaries.A_D，sigmaAuxiliaries.A_b，sigmaAuxiliaries.A_X，sigmaAuxiliaries.A_t）s。gMod（）;
        require（sigmaAuxiliaries.c == proof.c，“ Sigma协议质询相等性失败。”）；

        IPAuxiliaries内存ipAuxiliaries；
        ipAuxiliaries.o =  uint256（keccak256（ABI。编码（sigmaAuxiliaries.c）））。gMod（）;
        ipAuxiliaries.u_x =实用程序。g（）。pMul（ipAuxiliaries.o）；
        ipAuxiliaries.hPrimes = 新的实用程序。G1Point []（64）;
        对于（uint256 i = 0 ; i <  64 ; i ++）{
            ipAuxiliaries.hPrimes [i] = ip。hs（i）。pMul（zetherAuxiliaries.ys [i] 。gInv（））;
            ipAuxiliaries.hPrimeSum = ipAuxiliaries.hPrimeSum。pAdd（ipAuxiliaries.hPrimes [i] 。pMul（zetherAuxiliaries.ys [i] 。gMul（zetherAuxiliaries.z）。gAdd（zetherAuxiliaries.twoTimesZSquared [i]）））;
        }
        ipAuxiliaries.P =证明BA。PADD（proof.BS。PMUL（zetherAuxiliaries.x））。pAdd（gSum（）。pMul（zetherAuxiliaries.z。gNeg（）））。pAdd（ipAuxiliaries.hPrimeSum）;
        ipAuxiliaries.P = ipAuxiliaries.P。PADD（utils的。ħ（）。PMUL（proof.mu。gNeg（）））;
        ipAuxiliaries.P = ipAuxiliaries.P。PADD（ipAuxiliaries.u_x PMUL（proof.tHat））;
        要求（ip.verifyInnerProduct（ipAuxiliaries.hPrimes，ipAuxiliaries.u_x，ipAuxiliaries.P，proof.ipProof，ipAuxiliaries.o），“内部产品证明验证失败。”）；

        返回 true ;
    }

    函数assemblePolynomials（uint256 [ 2 ] [] memory  f）内部 视图 返回（uint256 [ 2 ] [] memory  result）{
        uint256 m = f。长度 /  2 ;
        uint256 N = 2  ** m;
        结果= 新的 uint256 [ 2 ] []（N）;
        对于（uint256 i = 0 ; i <  2 ; i ++）{
            uint256 []内存一半=递归多项式（i * m，（i +  1）* m，1，f）;
            对于（uint256 j = 0 ; j < N; j ++）{
                结果[j] [i] =一半[j]；
            }
        }
    }

    功能recursivePolynomials（uint256 基线，uint256 电流，uint256  ACCUM，uint256 [ 2 ] []存储器 ˚F）内部 视图 返回（uint256 []存储 结果）{
        //必须做一堆重新分配，因为坚固性不会让我拥有内部的东西，而且还会修改（内部）状态。（？）
        uint256大小= 2  **（当前-基线）；//大小至少为2 ...
        结果= 新的 uint256 []（大小）;

        如果（当前==基准）{
            result [ 0 ] =累加；
            返回结果；
        }
        电流=电流-  1 ;

        uint256 []剩余内存=递归多项式（基线，当前值，累积gMul（f [当前] [ 0 ]），f）；
        uint256 []内存权=递归多项式（基线，当前，累积gMul（f [当前] [ 1 ]），f）；
        对于（uint256 i = 0 ; i < size /  2 ; i ++）{
            result [i] = left [i];
            result [i + size /  2 ] = right [i];
        }
    }

    函数assembleConvolutions（uint256 [ 2 ] []内存 指数，Utils.G1Point []内存基数）内部 视图 返回（Utils.G1Point [ 2 ] []内存结果）{
        //指数是两个“行”（实际上是列）。
        //将返回两行，每行的长度为指数的一半；
        //即，我们将通过“指数”行的偶数循环移位来返回“基数”的Hadamards。
        uint256大小=指数。长度;
        uint256一半=大小/  2 ;
        结果= 新的实用程序。G1Point [ 2 ] []（一半）; //假设即使在return声明为最高的情况下这也是必要的

        Utils.G1Point [] memory base_fft =  fft（base，false）;

        uint256 []内存exponent_fft =新的 uint256 []（大小）;
        对于（uint256 i = 0 ; i <  2 ; i ++）{
            for（uint256 j = 0 ; j < size; j ++）{
                exponent_fft [j] = exponent [（size - j）％ size] [i]; //卷积​​翻转加复制
            }

            exponent_fft =  fft（exponent_fft）;
            Utils.G1Point []内存inverse_fft = 新的Utils。G1Point []（一半）;
            uint256补偿= 2 ;
            补偿=补偿。gInv（）;
            for（uint256 j = 0 ; j < half; j ++）{ //哈达玛
                inverse_fft [j] = base_fft [j]。pMul（exponent_fft [j]）。pAdd（base_fft [j + half] 。pMul（exponent_fft [j + half]））。pMul（补偿）；
            }

            inverse_fft =  fft（inverse_fft，true）;
            for（uint256 j = 0 ; j < half; j ++）{
                结果[j] [i] = inverse_fft [j];
            }
        }
    }

    函数fft（Utils.G1Point []内存输入，布尔 反向）内部 视图 返回（Utils.G1Point []内存结果）{
        uint256大小=输入。长度;
        如果（大小==  1）{
            返回输入；
        }
        require（size ％ 2  ==  0，“输入大小不是2的幂！”）;

        uint256 omega =团结。gExp（2 ** 28  /大小）;
        uint256补偿= 1 ;
        如果（反）{
            欧米茄=欧米茄。gInv（）;
            补偿=  2 ;
        }
        补偿=补偿。gInv（）;
        Utils.G1Point []内存甚至=  fft（提取（输入，0），取反）；
        Utils.G1Point []内存奇数=  fft（提取（输入，1），取反）；
        uint256 omega_run = 1 ;
        结果= 新的实用程序。G1Point []（size）;
        对于（uint256 i = 0 ; i < size /  2 ; i ++）{
            Utils.G1Point内存温度=奇数[i]。pMul（omega_run）;
            结果[i] =偶数[i]。p添加（温度）。pMul（补偿）；
            结果[i +大小/  2 ] =偶数[i]。pAdd（温度pNeg（））。pMul（补偿）；
            omega_run = omega_run。gMul（Ω）;
        }
    }

    函数提取（Utils.G1Point []内存输入，uint256 奇偶校验）内部 纯 返回（Utils.G1Point []内存结果）{
        结果= 新的实用程序。G1Point []（输入长度 /  2）;
        for（uint256 i = 0 ; i <输入长度 /  2 ; i ++）{
            result [i] =输入[ 2  * i +奇偶校验]；
        }
    }

    函数fft（uint256 []存储器 输入）内部 视图 返回（uint256 []存储器 结果）{
        uint256大小=输入。长度;
        如果（大小==  1）{
            返回输入；
        }
        require（size ％ 2  ==  0，“输入大小不是2的幂！”）;

        uint256 omega =团结。gExp（2 ** 28  /大小）;
        uint256 [] memory even = fft（extract（input，0））;
        uint256 []内存奇数= fft（提取（输入，1））;
        uint256 omega_run = 1 ;
        结果= 新的 uint256 []（大小）;
        对于（uint256 i = 0 ; i < size /  2 ; i ++）{
            uint256 temp =奇数[i]。gMul（omega_run）;
            结果[i] =偶数[i]。gAdd（temp）;
            结果[i +大小/  2 ] =偶数[i]。gSub（temp）;
            omega_run = omega_run。gMul（Ω）;
        }
    }

    函数提取（uint256 []存储器 输入，uint256 奇偶校验）内部 纯 返回（uint256 []存储器 结果）{
        结果= 新的 uint256 []（输入长度 /  2）;
        for（uint256 i = 0 ; i <输入长度 /  2 ; i ++）{
            result [i] =输入[ 2  * i +奇偶校验]；
        }
    }

    函数反序列化（字节 内存 arr）内部 纯 返回（TransferProof内存证明）{
        proof.BA =实用程序。G1Point（utils的。切片（ARR，0），utils的。切片（ARR，32））;
        proof.BS =实用程序。G1Point（utils的。切片（ARR，64），utils的。切片（ARR，96））;
        证明A =实用程序。G1Point（utils的。切片（ARR，128），utils的。切片（ARR，160））;
        证明B =实用工具 G1Point（utils的。切片（ARR，192），utils的。切片（ARR，224））;

        uint256 M =（ARR长度 -  1472）/  576 ;
        proof.CLnG = 新的实用程序。G1Point []（m）;
        proof.CRnG = 新的实用程序。G1Point []（m）;
        proof.C_0G = 新的实用程序。G1Point []（m）;
        proof.DG = 新的实用程序。G1Point []（m）;
        proof.y_0G = 新的实用程序。G1Point []（m）;
        proof.gG = 新的实用程序。G1Point []（m）;
        proof.C_XG = 新的实用程序。G1Point []（m）;
        proof.y_XG = 新的实用程序。G1Point []（m）;
        proof.f = 新的 uint256 []（2  * m）;
        对于（uint256 k = 0 ; k < m; k ++）{
            proof.CLnG [k] =实用程序。G1Point（utils的。切片（ARR，256  + ķ *  64），utils的。切片（ARR，288  + ķ *  64））;
            proof.CRnG [k] =实用程序。G1Point（Utils slice（arr，256  +（m + k）*  64），Utils slice（arr，288  +（m + k）*  64））;
            proof.C_0G [k] =实用程序。G1Point（Utils slice（arr，256  + m *  128  + k *  64），Utils slice（arr，288  + m *  128  + k *  64））;
            proof.DG [k] =实用程序。G1Point（实用程序切片（arr，256  + m *  192  + k *  64），实用程序切片（arr，288  + m *  192  + k *  64））;
            proof.y_0G [k] =实用程序。G1Point（Utils slice（arr，256  + m *  256  + k *  64），Utils slice（arr，288  + m *  256  + k *  64））;
            proof.gG [k] =实用程序。G1Point（实用程序切片（arr，256  + m *  320  + k *  64），实用程序切片（arr，288  + m *  320  + k *  64））;
            proof.C_XG [k] =实用程序。G1Point（Utils slice（arr，256  + m *  384  + k *  64），Utils slice（arr，288  + m *  384  + k *  64））;
            proof.y_XG [k] =实用程序。G1Point（实用程序切片（arr，256  + m *  448  + k *  64），实用程序切片（arr，288  + m *  448  + k *  64））;
            proof.f [k] =  uint256（实用切片（arr，256  + m *  512  + k *  32））;
            proof.f [k + m] =  uint256（实用切片（arr，256  + m *  544  + k *  32））;
        }
        uint256起始= m *  576 ;
        proof.z_A =  uint256（实用程序切片（arr，256  +起始））;

        proof.tCommits = [实用程序。G1Point（实用程序切片（arr，288  +起始），实用程序切片（arr，320  +起始）），实用程序。G1Point（实用程序片（arr，352  +起始），实用程序片（arr，384  +起始））]；
        proof.tHat =  uint256（实用程序切片（arr，416  +起始））；
        proof.mu =  uint256（实用程序切片（arr，448  +起始））;

        proof.c =  uint256（实用程序切片（arr，480  +起始））;
        proof.s_sk =  uint256（实用程序切片（arr，512  +起始））;
        proof.s_r =  uint256（实用程序切片（arr，544  +起始））;
        proof.s_b =  uint256（实用程序切片（arr，576  +起始））;
        proof.s_tau =  uint256（实用程序切片（arr，608  +起始））;

        InnerProductVerifier.InnerProductProof内存ipProof;
        ipProof.ls = 新的实用程序。G1Point []（6）;
        ipProof.rs = 新的实用程序。G1Point []（6）;
        for（uint256 i = 0 ; i <  6 ; i ++）{ // 2 ^ 6 = 64。
            ipProof.ls [i] =实用程序。G1Point（实用程序片（arr，640  +起始+ i *  64），实用程序片（arr，672  +起始+ i *  64））;
            ipProof.rs [i] =实用程序。G1Point（实用程序切片（arr，640  +起始+（6  + i）*  64），实用程序切片（arr，672  +起始+（6  + i）*  64））;
        }
        ipProof.a =  uint256（实用程序切片（arr，640  +开头+  6  *  128））;
        ipProof.b =  uint256（实用程序切片（arr，672  +开头+  6  *  128））;
        proof.ipProof = ipProof;

        退货证明;
    }
}
