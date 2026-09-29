import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-629733887497550766539689/400000000000000000000000)
  B := (98054846972169651397877033/1000000000000000000000000000)
  C := (44632727681534166419563547/10000000000000000000000000000)
  dδ := (31512611527019507295932499/500000000000000000000000000)
  dM := (10502521955895239604006353/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12280915005257407202066133/1000000000000000000000000), (12518437066919125832953341/10000000000000000000000000), (16314205103318688117042257/1000000000000000000000000), (56520149515702229336966411/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94453/178928)
  hi := (47239/89464)
  vmin := (1994666775/8003807296)
  damping := (1994666775/8003807296)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell141
