# 代数同调泛系数定理

设 R 为 PID，C 为逐阶自由的 ℤ 分次链复形，D 为任意 R-模。已证明

0 → H_n(C) ⊗_R D → H_n(C ⊗_R D) → Tor'_1(H_(n-1)(C),D) → 0

短正合且存在分裂，并给出非规范直和同构。不要求有限秩，也不限制 D 自由或平坦。
Tor' 是 Mathlib 对第一变量导出的标准 Tor。

主文件：UniversalCoefficient/AlgebraicUCT.lean。
主声明：algebraic_uct、algebraicUCT_shortExact、algebraicUCTSplitting、algebraicUCTDirectSumIso。

使用固定 Lean v4.35.0-rc4 和 lake-manifest.json 中的 Mathlib 版本：

```powershell
lake build
lake env lean Audit.lean
```

Audit.lean 检查主定理类型及传递公理；允许的标准公理为 propext、Classical.choice、Quot.sound。
当前证明包括短正合与分裂存在，不包含主序列自然性的形式化。
.lake/packages 联接已有本机缓存；迁移机器时需安装固定依赖。

## License

Copyright 2026 rushusuixing. Licensed under Apache-2.0; see LICENSE and NOTICE.

CI builds the project and runs `python3 scripts/check_axioms.py` to check the four main UCT declarations.
