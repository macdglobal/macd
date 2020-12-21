// SPDX-License-Identifier：MIT
语用固结度^ 0。6。0 ;


抽象 合同ZicoToken {

    函数testFunc（）返回虚拟 公共 视图  （字符串内存）； 
}

合约ETHToken是ZicoToken {
    uint  public myBalance;

    建设者（）公众 应付款{
        myBalance =  msg。价值;
    }

    功能takeETH（）公共 应付款项{
        myBalance + =  msg。价值;
    }

    函数testFunc（）覆盖 公共 视图  返回（字符串 存储器）{
        返回 “ ETHToken”；
    }

}

合约ETHToken2是ZicoToken {
    函数testFunc（）覆盖 公共 视图  返回（字符串 存储器）{
        返回 “ ETHToken2”；
    }
}

合同测试{
    ZicoToken令牌；

    构造函数（address  _token）public {
        令牌=  ZicoToken（_token）;
    }

    函数execFunc（）公共 视图 返回（字符串 存储器）{
        返回令牌。testFunc（）;
    }
}
