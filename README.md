# algebraic-topology

## English

Formalizations of algebraic topology and its algebraic foundations in Lean 4 and Mathlib. Each subproject maintains its own Lake configuration and pinned dependency versions.

### Subprojects

- [algebraic-universal-coefficient-theorem](algebraic-universal-coefficient-theorem/README.md): the algebraic universal coefficient theorem for homology over a PID, including the short exact sequence, existence of a splitting, and a noncanonical direct sum decomposition.

```text
algebraic-topology/
├── algebraic-universal-coefficient-theorem/
│   ├── UniversalCoefficient/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── README.md
├── .github/workflows/
├── LICENSE
└── NOTICE
```

See the subproject README for build and axiom audit commands. GitHub Actions runs the build and axiom audit in the subproject directory.

## 中文

使用 Lean 4 与 Mathlib 形式化代数拓扑及其代数基础。各子项目独立维护 Lake 配置和固定依赖版本。

### 子项目

- [algebraic-universal-coefficient-theorem](algebraic-universal-coefficient-theorem/README.md)：PID 上的代数同调泛系数定理，包括短正合列、存在分裂与非规范直和形式。

```text
algebraic-topology/
├── algebraic-universal-coefficient-theorem/
│   ├── UniversalCoefficient/
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── README.md
├── .github/workflows/
├── LICENSE
└── NOTICE
```

构建与审计命令见子项目说明。GitHub Actions 在子项目目录中运行构建及公理审计。

## License

Copyright 2026 rushusuixing. Licensed under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
