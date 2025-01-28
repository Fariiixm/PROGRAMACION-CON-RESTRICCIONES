(declare-const x1 Int)  ; VM 1 está en el servidor x1
(declare-const x2 Int)  ; VM 2 está en el servidor x2
(declare-const x3 Int)  ; VM 3 está en el servidor x3

(declare-const y1 Bool)
(declare-const y2 Bool)
(declare-const y3 Bool)

; Una maquina virtul está en un servidor

(assert (<= x1 3))
(assert (<= 1 x1))
(assert (<= x2 3))
(assert (<= 1 x2))
(assert (<= x3 3))
(assert (<= 1 x3))


(assert (=> y1 (or (= x1 1) (= x2 1) (= x3 1))))
(assert (=> y2 (or (= x1 2) (= x2 2) (= x3 2))))
(assert (=> y3 (or (= x1 3) (= x2 3) (= x3 3))))


; Constraints de capacidad 

(assert (<= (+ (* 100 (ite (= x1 1) 1 0)) 
               (* 50 (ite (= x2 1) 1 0)) 
               (* 15 (ite (= x3 1) 1 0))) 
            (* 100 (ite y1 1 0))))
(assert (<= (+ (* 100 (ite (= x1 2) 1 0)) 
               (* 50 (ite (= x2 2) 1 0)) 
               (* 15 (ite (= x3 2) 1 0))) 
            (* 75 (ite y2 1 0))))             
(assert (<= (+ (* 100 (ite (= x1 3) 1 0)) 
               (* 50 (ite (= x2 3) 1 0)) 
               (* 15 (ite (= x3 3) 1 0))) 
            (* 150 (ite y3 1 0))))

; Objetivos de optimización

; minimizar uso servidores
(assert-soft (not y1) :id num_servers :weight 1)
(assert-soft (not y2) :id num_servers :weight 1)
(assert-soft (not y3) :id num_servers :weight 1)

; minimizar coste
(assert-soft (not y1) :id costs :weight 10)
(assert-soft (not y2) :id costs :weight 5)
(assert-soft (not y3) :id costs :weight 20)

(check-sat)

;pedimos la solución
(get-value (x1) )
(get-value (x2) )
(get-value (x3) )

(get-value (y1) )
(get-value (y2) )
(get-value (y3) )

