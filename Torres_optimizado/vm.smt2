(declare-fun x11 () Bool) ;VM 1 está en servidor 1 
(declare-fun x12 () Bool) ;VM 1 está en servidor 2 
(declare-fun x13 () Bool) ;VM 1 está en servidor 3 
(declare-fun x21 () Bool) ;VM 2 está en servidor 1 
(declare-fun x22 () Bool) ;VM 2 está en servidor 2 
(declare-fun x23 () Bool) ;VM 2 está en servidor 3 
(declare-fun x31 () Bool) ;VM 3 está en servidor 1 
(declare-fun x32 () Bool) ;VM 3 está en servidor 2 
(declare-fun x33 () Bool) ;VM 3 está en servidor 3 

(declare-fun y1 () Bool) ; servior 1 está en uso
(declare-fun y2 () Bool)
(declare-fun y3 () Bool)

; Una maquina virtul está exactamente en un servidor
(assert (= (+ (+ (ite x11 1 0) (ite x12 1 0)) (ite x13 1 0)) 1))
(assert (= (+ (+ (ite x21 1 0) (ite x22 1 0)) (ite x23 1 0)) 1))
(assert (= (+ (+ (ite x31 1 0) (ite x32 1 0)) (ite x33 1 0)) 1))

; Un servidor está usado si tiene una máquina virtual creada en él.
;(assert (=> x11 y1))
;(assert (=> x21 y1))
;(assert (=> x31 y1))
;(assert (=> x12 y2))
;(assert (=> x22 y2))
;(assert (=> x32 y2))
;(assert (=> x13 y3))
;(assert (=> x23 y3))
;(assert (=> x33 y3))

;(assert (<= (ite y1 1 0) (+ (+ (ite x11 1 0) (ite x12 1 0)) (ite x13 1 0)) ))

(assert (=> y1 (or x11 (or x12 x13))) )
(assert (=> y2 (or x21 (or x22 x23))) )
(assert (=> y3 (or x31 (or x32 x33))) )

; Constraints de capacidad 

(assert (<= (+ (* 100 (ite x11 1 0)) 
               (* 50 (ite x21 1 0)) 
               (* 15 (ite x31 1 0))) 
            (* 100 (ite y1 1 0))))
(assert (<= (+ (* 100 (ite x12 1 0)) 
               (* 50 (ite x22 1 0)) 
               (* 15 (ite x32 1 0))) 
            (* 75 (ite y2 1 0))))             
(assert (<= (+ (* 100 (ite x13 1 0)) 
               (* 50 (ite x23 1 0)) 
               (* 15 (ite x33 1 0))) 
            (* 150 (ite y3 1 0))))

; Objetivos de optimización

; minimizar uso servidores
(assert-soft (not y1) :id num_servers)
(assert-soft (not y2) :id num_servers)
(assert-soft (not y3) :id num_servers)

; minimizar coste
(assert-soft (not y1) :id costs :weight 10)
(assert-soft (not y2) :id costs :weight 5)
(assert-soft (not y3) :id costs :weight 20)

(check-sat)

;pedimos la solución
(get-value (x11) )
(get-value (x12) )
(get-value (x13) )
(get-value (x21) )
(get-value (x22) )
(get-value (x23) )
(get-value (x31) )
(get-value (x32) )
(get-value (x33) )

(get-value (y1) )
(get-value (y2) )
(get-value (y3) )

