// SPDX-License-Identifier：MIT
语用固结度^ 0。6。0 ;

合同迁移{
  向 公共所有者讲话；
  uint  public last_completed_migration;

  修饰符限制（）{
    如果（味精。发件人 ==所有者）_;
  }

  构造函数（）public {
    所有者= 味精。发件人;
  }

  函数setCompleted（完成uint的操作 ）public受限制的{
    last_completed_migration =已完成；
  }

  功能升级（地址 new_address）公共限制{
    迁移升级= 迁移（new_address）；
    升级。setCompleted（last_completed_migration）;
  }
}
