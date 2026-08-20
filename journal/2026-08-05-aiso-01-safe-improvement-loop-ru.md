# AISO-01: оптимизация только внутри допустимого множества

Новый слой отделяет качество предложения от права действовать.

`D_t = {delta in A_t | Improve>0 and Risk<=rho and Validate and Permit and Safe and PreservesInv and RollbackWitness}`

`delta*_t = argmax_(delta in D_t) [alpha Improve - beta Risk - gamma Cost - lambda Entropy]`

Если `D_t` пусто, выбирается `NO_OP`. Даже выбранное действие не обучает модель само по себе: CSS должен применить его, постпроверка должна пройти, защищённые инварианты должны сохраниться, после чего выпускается квитанция. Ошибка постпроверки активирует предъявленное свидетельство отката и блокирует обучение.

Это формальный контракт выбора, а не заявление о физической полноте модели риска или функции качества.

Код: [Lean-ядро](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/AISOControlLoop.lean) · [исполняемый селектор](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/aiso-control-loop.mjs) · [слепой корпус](https://github.com/kernelpanic888/TMI-Lean-Formal-Library/blob/main/tools/tests/aiso-control-loop.test.mjs)

Опоры: [Constrained Policy Optimization](https://arxiv.org/abs/1705.10528) · [Shielding](https://arxiv.org/abs/1708.08611) · [Simplex](https://www.sei.cmu.edu/library/an-architectural-description-of-the-simplex-architecture/) · [NIST AI RMF](https://doi.org/10.6028/NIST.AI.100-1)

