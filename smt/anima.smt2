(set-logic UF)

(set-option :produce-models true)
(set-option :finite-model-find true)

(declare-sort Anima 0)
(declare-const gottlob Anima)
(declare-const a Anima)

(declare-sort Direction 0)

(declare-const up Direction)
(declare-const right Direction)
(declare-const down Direction)
(declare-const left Direction)

(assert (distinct up right down left))

(declare-fun is_facing (Anima Direction) Bool)

(assert (forall ((a Anima)) (xor (is_facing a up)
                            (xor (is_facing a right)
                            (xor (is_facing a down)
                                 (is_facing a left))))))

(check-sat)
(get-model)
(get-value ((is_facing gottlob up)))
(get-value ((is_facing gottlob right)))
(get-value ((is_facing gottlob down)))
(get-value ((is_facing gottlob left)))
(exit)
