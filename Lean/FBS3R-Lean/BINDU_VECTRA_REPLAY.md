# Независимая пересборка BINDU VECTRA (2026-11-27)

Исходники: `PROOFS/BinduEventInterface/` из zip-пакета папки `2026_11_09_BINDU_VECTRA_…` (53 файла) и `PhysicalExactDiamond.LEAN_VERIFIED.lean`.
Окружение: Lean 4.19.0, Mathlib v4.19.0, собрано из исходников в облачном контейнере.
Команда: `lake build BinduEventInterface.BinduUnconditionalHybridCandidate BinduEventInterface.BinduSiteLocalFamilyBridgeCandidate`.

Результат: **Build completed successfully** (6705/6705 заданий), ошибок нет; скомпилированы все 53 модуля пакета.
Все 101 директив `#print axioms` в пакете выдают только стандартные аксиомы; `sorryAx`, `Lean.ofReduceBool` и пользовательских аксиом нет.

| Целевая теорема | Аксиомы |
|---|---|
| `bindu_site_local_family_bridge` | propext, Classical.choice, Quot.sound |
| `bindu_site_replacer_kernel_bridge` | propext, Classical.choice, Quot.sound |
| `bindu_site_pauli_z_kernel_bridge` | propext, Classical.choice, Quot.sound |
| `bindu_local_dephasing_half_Z` | propext, Classical.choice, Quot.sound |
| `bindu_site_dephasing_kernel_bridge` | propext, Classical.choice, Quot.sound |
| `bindu_global_site_identity_unconditional` | propext, Classical.choice, Quot.sound |
| `bindu_global_hybrid_rplusr2_unconditional` | propext, Classical.choice, Quot.sound |
| `bindu_nQubit_diamond_envelope_unconditional` | propext, Classical.choice, Quot.sound |

Оговорка. Lean проверяет теоремы о собственных определениях пакета. `schattenOneSpectralNorm X = Σᵢ √λᵢ(X†X)`, то есть настоящая норма следа. Соответствие каналов физическим устройствам и оценки мощности моделей Lean не проверяет.
