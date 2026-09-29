import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 90
  A := (-15903307614096612765308691/10000000000000000000000000)
  B := (24441622817531850897498913/250000000000000000000000000)
  C := (462382950821673123996923/156250000000000000000000000)
  dδ := (31026749162005311244438843/500000000000000000000000000)
  dM := (2592148574689402684700923/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6184939206498313524207333/500000000000000000000000), (52064403131454142226175463/1000000000000000000000000), (23916303446700805324098837/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27/52)
  hi := (22597/43472)
  vmin := (471712375/1889814784)
  damping := (471712375/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell106
