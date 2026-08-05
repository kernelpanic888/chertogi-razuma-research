# K-00: интерфейсное замыкание

`Act_I(a,b)=V_A(a) and V_B(b) and C_I(a,b)`

`Exec_I(a,b)=some(a,b)` при совпадении тройки; иначе `none`.

Два проверенных состояния ещё не образуют акт. Тройку замыкает предикат совместимости интерфейса. Совпало всё трижды, есть неизменённый кандидат действия. Не совпало хотя бы одно условие, наступает тишина. Lean доказывает семантику этой связки, а исполнимый тест покрывает все восемь бинарных комбинаций.

[Lean-ядро](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AISOValidationKernel.lean) · [таблица истинности](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/aiso-validation-kernel.test.mjs)
