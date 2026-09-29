import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 45
  A := (-2115771188288372095342993/20000000000000000000000000)
  B := (594715620658345725524363/20000000000000000000000000)
  C := (-10896286606791889123302397/125000000000000000000000000)
  dδ := (24386346860509059558674849/1000000000000000000000000000)
  dM := (24829727283204983774231311/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(3546515794173054070270723/1250000000000000000000000), (15474863930238177189835369/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (103/255)
  hi := (7/17)
  vmin := (15656/65025)
  damping := (15656/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell020
