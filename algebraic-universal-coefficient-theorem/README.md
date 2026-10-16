# algebraic-universal-coefficient-theorem

代数同调泛系数定理，是 [algebraic-topology](../README.md) 的子项目。

设 R 为 PID，C 为逐阶自由的 ℤ 分次链复形，D 为任意 R-模。已证明短正合列

$$
0 \longrightarrow H_n(C)\otimes_R D
\longrightarrow H_n(C\otimes_R D)
\longrightarrow \operatorname{Tor}_1^R(H_{n-1}(C),D)
\longrightarrow 0.
$$

该列存在分裂，并给出非规范直和同构。不要求有限秩，也不限制 D 自由或平坦。
代码使用 Mathlib 对第一变量导出的标准 `Tor'`。

主文件：[AlgebraicUCT.lean](UniversalCoefficient/AlgebraicUCT.lean)。
主声明：`algebraic_uct`、`algebraicUCT_shortExact`、`algebraicUCTSplitting`、`algebraicUCTDirectSumIso`。

安装 [Lean/Elan](https://leanprover-community.github.io/get_started.html) 和 Git 后运行：

```sh
git clone https://github.com/rushusuixing/algebraic-topology.git
cd algebraic-topology/algebraic-universal-coefficient-theorem
lake exe cache get
lake build
lake env lean Audit.lean
```

`lean-toolchain` 和 `lake-manifest.json` 固定 Lean v4.35.0-rc4 及 Mathlib 版本。
依赖由 Lake 获取，`.lake/` 不纳入版本控制。

CI 在独立环境构建项目，并运行 `python3 scripts/check_axioms.py` 检查四个主声明的传递公理。
允许的标准公理为 `propext`、`Classical.choice`、`Quot.sound`；遇到 `sorryAx` 或其他公理会失败。
当前证明包括短正合与分裂存在，不包含主序列自然性的形式化。

## License

Copyright 2026 rushusuixing. Licensed under Apache-2.0; see [LICENSE](../LICENSE) and [NOTICE](../NOTICE).
