# 每个 lean 文件/关卡的设置
在模板给出的示例中，`Metadata.lean` 将包含所有文件/关卡共同的设置，应该在每个 lean 文件的开头导入。

`Metadata.lean` 可以包含 `Mathlib`/`Lean` 导入、`theorem`、`axiom`。此外，`Metadata.lean` 可以分成多个具有类似设置的文件，其中 `Metadata.lean` 只是导入这些文件。这可以用来组织和隔离相关的内容。例如，一个文件包含 mathlib 导入，另一个包含定理、公理等。

# 公理
在 `Metadata.lean` 中有公理，可以通过 `open namespace` 在 lean 文件中使用，其中 `namespace` 是声明公理的地方。但是，您需要执行 `NewTheorem namespace.axiom` 才能将其作为定理引入。

## 示例
假设您在 `Metadata.lean` 中有以下内容，
```
import Mathlib
namespace setup
axiom important_theorem : 2=2
end setup
```

在关卡对应的 lean 文件中，您会有
```
...
-- 允许在 lean 文件中使用
open setup

-- 将其添加到游戏中
NewTheorem setup.important_theorem
```
