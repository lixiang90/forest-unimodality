import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell128.Parameters
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch000_049
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch050_099
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch100_149
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23607_44732.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree000.table
  base := (2958507633728080451540165553/50000000000000000000000000)
  polynomial :=
    { denominator := 223660000000000000000000000000000000000000000
      center := (1497457)
      previous := (0)
      next := (1343025)
      square := (34514115274326112322578196750000000000000000)
      linear := (-161741774133212552679861317352800000000000000)
      constant := (13233996347192449475829468551679600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree000.table
  base := (2958507633728080451540165553/50000000000000000000000000)
  polynomial :=
    { denominator := 447320000000000000000000000000000000000000000
      center := (2998089)
      previous := (0)
      next := (2682875)
      square := (69028230548652224645156393500000000000000000)
      linear := (-323483548266425105359722634705600000000000000)
      constant := (26467992694384898951658937103359200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree001.table
  base := (178437072900008136635504703006685523560611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-2215714193331295167014408629835612400000000000000)
      constant := (90321815604032710431669563318536665540749888751116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree001.table
  base := (178313094200111732442501113287273245996451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-4432291239544448486836881714589974800000000000000)
      constant := (180522070400848135272753058719363199831499662988312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49922973248514476683/100000000000000000000)
  directionHi := (12480743312128619171/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree002.table
  base := (44927249247629089324475329147538966665821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-2622670126530874357409928147714862400000000000000)
      constant := (58521966999675165626918048402414402588156080254690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree002.table
  base := (224357892904431569420698068193235568714147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-5247065958825465020435985205267224800000000000000)
      constant := (116910555134814759919535698976437948520062443563532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922973248514476683/100000000000000000000)
  centralHi := (12480743312128619171/25000000000000000000)
  directionLo := (70601745842038383419/100000000000000000000)
  directionHi := (3530087292101919171/5000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree003.table
  base := (148564339019778645615756031290786623422869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-3029626059730453547805447665594112400000000000000)
      constant := (40984839703645259001496107787834180766598856107882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree003.table
  base := (74162673997318034013912595672041139177769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-6061840678106481554035088695944474800000000000000)
      constant := (81860288452982152739751695067398592270397370400328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70601745842038383419/100000000000000000000)
  centralHi := (3530087292101919171/5000000000000000000)
  directionLo := (21617281532832239199/25000000000000000000)
  directionHi := (86469126131328956797/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree004.table
  base := (808194308928519729979253878499809696953/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-3436581992930032738200967183473362400000000000000)
      constant := (31405046183277165821357718257415027148335881476352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree004.table
  base := (103261302232665755511912550270084551289189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-6876615397387498087634192186621724800000000000000)
      constant := (62731632142181489668862268561579943084081070257684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21617281532832239199/25000000000000000000)
  centralHi := (86469126131328956797/100000000000000000000)
  directionLo := (49922973248514476683/50000000000000000000)
  directionHi := (99845946497028953367/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree005.table
  base := (15113749375340969777605334700592384806033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-3843537926129611928596486701352612400000000000000)
      constant := (26350679697236211168934561536362990911338510971370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree005.table
  base := (37712699870772800333746527554095534615403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-7691390116668514621233295677298974800000000000000)
      constant := (52651138663802193633608346400620889579472885672536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49922973248514476683/50000000000000000000)
  centralHi := (99845946497028953367/100000000000000000000)
  directionLo := (3488473806955683493/3125000000000000000)
  directionHi := (111631161822581871777/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree006.table
  base := (57431288784179454871095269317598617582537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-4250493859329191118992006219231862400000000000000)
      constant := (23947679722598509690446850299818368043956985087186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree006.table
  base := (14330240669648972285738321505627571046433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-8506164835949531154832399167976224800000000000000)
      constant := (47868685217031674764074966143645188350049700043792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/3125000000000000000)
  centralHi := (111631161822581871777/100000000000000000000)
  directionLo := (122285810901475206619/100000000000000000000)
  directionHi := (6114290545073760331/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree007.table
  base := (22462470221280422260381124969814061863409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-4657449792528770309387525737111112400000000000000)
      constant := (23167667868878033862779522331013187306609269352004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree007.table
  base := (44837708165328602003759681994657823363739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-9320939555230547688431502658653474800000000000000)
      constant := (46328152296153290097961761413414962328885841877484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122285810901475206619/100000000000000000000)
  centralHi := (6114290545073760331/5000000000000000000)
  directionLo := (4127617872640614369/3125000000000000000)
  directionHi := (132083771924499659809/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree008.table
  base := (35777075371616035424095919134662147311541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-5064405725728349499783045254990362400000000000000)
      constant := (23442217123463172922918127783995799860848082525098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree008.table
  base := (2231595963807498465690336618273953695627/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-10135714274511564222030606149330724800000000000000)
      constant := (46893949326653756036296780481949235915825545894592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4127617872640614369/3125000000000000000)
  centralHi := (132083771924499659809/100000000000000000000)
  directionLo := (70601745842038383419/50000000000000000000)
  directionHi := (141203491684076766839/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree009.table
  base := (1435890619741642986243321807494819115231/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-5471361658927928690178564772869612400000000000000)
      constant := (24453706104303265842098007956572042047928839078360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree009.table
  base := (3582113087033513855254910173579625213611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-10950488993792580755629709640007974800000000000000)
      constant := (48932004815293585966301025941966494810822640152928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70601745842038383419/50000000000000000000)
  centralHi := (141203491684076766839/100000000000000000000)
  directionLo := (149768919745543430049/100000000000000000000)
  directionHi := (2995378394910868601/2000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree010.table
  base := (184208781168168668594972953179524405031/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-5878317592127507880574084290748862400000000000000)
      constant := (26021785555303862576500766501078635839051472289750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree010.table
  base := (11486270747341118301408922520807708568059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-11765263713073597289228813130685224800000000000000)
      constant := (52082510358045259551772091526620804206259042094808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149768919745543430049/100000000000000000000)
  centralHi := (2995378394910868601/2000000000000000000)
  directionLo := (157870303032960954689/100000000000000000000)
  directionHi := (15787030303296095469/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree011.table
  base := (18282922012936883776397634307985325389873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-6285273525327087070969603808628112400000000000000)
      constant := (28041653345537850781476705833168095725512486309794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree011.table
  base := (4558666177692874439127748822377876771769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-12580038432354613822827916621362474800000000000000)
      constant := (56136475988692634917988060357880543593718412256656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157870303032960954689/100000000000000000000)
  centralHi := (15787030303296095469/10000000000000000000)
  directionLo := (165575770684272561201/100000000000000000000)
  directionHi := (82787885342136280601/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree012.table
  base := (14236874067492664923531405882987556943873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-6692229458526666261365123326507362400000000000000)
      constant := (30450426705554440599246173822778224129518318121794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree012.table
  base := (2838532241122680468678949386912400460901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-13394813151635630356427020112039724800000000000000)
      constant := (60968535502874380644590171756242359388072870791780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165575770684272561201/100000000000000000000)
  centralHi := (82787885342136280601/50000000000000000000)
  directionLo := (172938252262657913593/100000000000000000000)
  directionHi := (86469126131328956797/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree013.table
  base := (1341334814934773374229947162255496431889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-7099185391726245451760642844386612400000000000000)
      constant := (33208768100501593390388501739409693239413786315536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree013.table
  base := (10689752386580035195694624901247463913941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-14209587870916646890026123602716974800000000000000)
      constant := (66500262297869751779509525240955461848493605744596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172938252262657913593/100000000000000000000)
  centralHi := (86469126131328956797/50000000000000000000)
  directionLo := (179999839871135988329/100000000000000000000)
  directionHi := (17999983987113598833/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree014.table
  base := (7660885754818693045250574004810547318503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-7506141324925824642156162362265862400000000000000)
      constant := (36290802818632436532954342154179884778924610849934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree014.table
  base := (1905696617699998175431132443222944665963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-15024362590197663423625227093394224800000000000000)
      constant := (72680055936657401569185248726208999768009735566512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179999839871135988329/100000000000000000000)
  centralHi := (17999983987113598833/10000000000000000000)
  directionLo := (93397330812511030149/50000000000000000000)
  directionHi := (186794661625022060299/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree015.table
  base := (2477806359394647120600144593056302707087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-7913097258125403832551681880145112400000000000000)
      constant := (39678551543763662759978671638494235159110467594172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree015.table
  base := (2460026374194885817620603902074628512341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-15839137309478679957224330584071474800000000000000)
      constant := (79472044000301897361602011399641900902945565229992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93397330812511030149/50000000000000000000)
  centralHi := (186794661625022060299/100000000000000000000)
  directionLo := (48337710996163738761/25000000000000000000)
  directionHi := (38670168796930991009/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree016.table
  base := (256213623773085438595703431627533169527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-8320053191324983022947201398024362400000000000000)
      constant := (43358827209582732405822272296096633130231939834060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree016.table
  base := (632230999184725922041355073108724111341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-16653912028759696490823434074748724800000000000000)
      constant := (86849900354534621506123476606636951660900553035984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48337710996163738761/25000000000000000000)
  centralHi := (38670168796930991009/20000000000000000000)
  directionLo := (199691892994057906733/100000000000000000000)
  directionHi := (99845946497028953367/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree017.table
  base := (219940959223963309040146477999122608861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-8727009124524562213342720915903612400000000000000)
      constant := (47321481390330630147248334547397043363650014128116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree017.table
  base := (102219202752534919196054424630795888911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-17468686748040713024422537565425974800000000000000)
      constant := (94793353654149627958426409978960839410488166823664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199691892994057906733/100000000000000000000)
  centralHi := (99845946497028953367/50000000000000000000)
  directionLo := (51459422962127503203/25000000000000000000)
  directionHi := (205837691848510012813/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree018.table
  base := (-57744702976431761490216321742594391673/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-9133965057724141403738240433782862400000000000000)
      constant := (51558393389270904312987195320039610992155438245150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree018.table
  base := (-1472530660415407773789884467596667576221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-18283461467321729558021641056103224800000000000000)
      constant := (103286175253604229207102890545348866179259732755724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51459422962127503203/25000000000000000000)
  centralHi := (205837691848510012813/100000000000000000000)
  directionLo := (211805237526115150257/100000000000000000000)
  directionHi := (105902618763057575129/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree019.table
  base := (-3115118181220379715165882149869586494939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-9540920990923720594133759951662112400000000000000)
      constant := (56062871037941512923927409437905704292603255147658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree019.table
  base := (-3142042679606670037433348416398657895639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-19098236186602746091620744546780474800000000000000)
      constant := (112314986657906334690580685053122275943142285326116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211805237526115150257/100000000000000000000)
  centralHi := (105902618763057575129/50000000000000000000)
  directionLo := (217609195351359060019/100000000000000000000)
  directionHi := (10880459767567953001/5000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree020.table
  base := (-919427556772659046526563952823516330293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-9947876924123299784529279469541362400000000000000)
      constant := (60829282186739289163924559453134357405504021997230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree020.table
  base := (-2311086211303279620900270140861904865311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-19913010905883762625219848037457724800000000000000)
      constant := (121868525921889169877834362313012813263820740111368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609195351359060019/100000000000000000000)
  centralHi := (10880459767567953001/5000000000000000000)
  directionLo := (3488473806955683493/1562500000000000000)
  directionHi := (223262323645163743553/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree021.table
  base := (-295445228981251244002543952531074392091/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-10354832857322878974924798987420612400000000000000)
      constant := (65852817498610405328030078249008336096164555940040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree021.table
  base := (-5932146492880122881315985110683260275669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-20727785625164779158818951528134974800000000000000)
      constant := (131937175168734556892810076519182799166283342907436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/1562500000000000000)
  centralHi := (223262323645163743553/100000000000000000000)
  directionLo := (114387901914286518767/50000000000000000000)
  directionHi := (45755160765714607507/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree022.table
  base := (-1413399983264806579986002949028193281417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-10761788790522458165320318505299862400000000000000)
      constant := (71129329663784644610377831792193173816327567840870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree022.table
  base := (-7088545668944946209192351475358623719457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-21542560344445795692418055018812224800000000000000)
      constant := (142512640063687970178384979911828688303605712890108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114387901914286518767/50000000000000000000)
  centralHi := (45755160765714607507/20000000000000000000)
  directionLo := (234159500502075776399/100000000000000000000)
  directionHi := (585398751255189441/250000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree023.table
  base := (-8085817781730839276141710460574637551121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-11168744723722037355715838023179112400000000000000)
      constant := (76655218472751500054073308118086920062993192725662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree023.table
  base := (-8105763338319057308741592976833166675069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-22357335063726812226017158509489474800000000000000)
      constant := (153587720487997475453012503111177747999456167281036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234159500502075776399/100000000000000000000)
  centralHi := (585398751255189441/250000000000000000)
  directionLo := (59855542210680832377/25000000000000000000)
  directionHi := (239422168842723329509/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree024.table
  base := (-2244477460777318662085387105859247412377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-11575700656921616546111357541058362400000000000000)
      constant := (82427344515322746283160766728198806501468480837176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree024.table
  base := (-2249087516392257445809986621027549665647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-23172109783007828759616262000166724800000000000000)
      constant := (165156138172897643911466186482507922942273045209872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59855542210680832377/25000000000000000000)
  centralHi := (239422168842723329509/100000000000000000000)
  directionLo := (122285810901475206619/50000000000000000000)
  directionHi := (244571621802950413239/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree025.table
  base := (-9754255583620288865529650057785340184727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-11982656590121195736506877058937612400000000000000)
      constant := (88442961614391198311899042930067712269613751550994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree025.table
  base := (-9771283575516655062943172037333176308351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-23986884502288845293215365490843974800000000000000)
      constant := (177212401643762092144416572066111372442522870029444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122285810901475206619/50000000000000000000)
  centralHi := (244571621802950413239/100000000000000000000)
  directionLo := (31201858280321547927/12500000000000000000)
  directionHi := (249614866242572383417/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree026.table
  base := (-5212240405816707215956093424701556365901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-12389612523320774926902396576816862400000000000000)
      constant := (94699662172605044823998308410376745933502895661644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree026.table
  base := (-10440187273276390113826110868654059113479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-24801659221569861826814468981521224800000000000000)
      constant := (189751696908086604253154443736591878797970092991076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31201858280321547927/12500000000000000000)
  centralHi := (249614866242572383417/100000000000000000000)
  directionLo := (127279107385372948041/50000000000000000000)
  directionHi := (254558214770745896083/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree027.table
  base := (-1374629838640806086419946992508301334739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-12796568456520354117297916094696112400000000000000)
      constant := (101195331888727151129118579869191187409112363386064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree027.table
  base := (-2752877844926569570792381194875165294403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-25616433940850878360413572472198474800000000000000)
      constant := (202769796844661404067476675052280314401862820158928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127279107385372948041/50000000000000000000)
  centralHi := (254558214770745896083/100000000000000000000)
  directionLo := (25940737839398687039/10000000000000000000)
  directionHi := (259407378393986870391/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree028.table
  base := (-1147936241087052555982313020012475633727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-13203524389719933307693435612575362400000000000000)
      constant := (107928111594685224948300977033620967672423004289940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree028.table
  base := (-11492685625783181413699413112671881115579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-26431208660131894894012675962875724800000000000000)
      constant := (216262984820048996335883618633877614892067761283476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25940737839398687039/10000000000000000000)
  centralHi := (259407378393986870391/100000000000000000000)
  directionLo := (264167543848999319617/100000000000000000000)
  directionHi := (132083771924499659809/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree029.table
  base := (-2375599021228610165152016244358697292037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-13610480322919512498088955130454612400000000000000)
      constant := (114896364714664340987245292941111873939521690109070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree029.table
  base := (-11890249472327449626932010108371493109263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-27245983379412911427611779453552974800000000000000)
      constant := (230227989547735267030383641844247031248354192213572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264167543848999319617/100000000000000000000)
  centralHi := (132083771924499659809/50000000000000000000)
  directionLo := (134421719302708733009/50000000000000000000)
  directionHi := (268843438605417466019/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree030.table
  base := (-6099350932956391766630698281465474574757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-14017436256119091688484474648333862400000000000000)
      constant := (122098649295005695763915237847061220314153589123308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree030.table
  base := (-1220996404571408178928526255272277843461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-28060758098693927961210882944230224800000000000000)
      constant := (244661929093638129028537513941381484081229813942840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134421719302708733009/50000000000000000000)
  centralHi := (268843438605417466019/100000000000000000000)
  directionLo := (136719692929691699943/50000000000000000000)
  directionHi := (273439385859383399887/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree031.table
  base := (-1244656629211980077020203949992588371153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-14424392189318670878879994166213112400000000000000)
      constant := (129533693830387478379850309744991123790325269583660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree031.table
  base := (-12456908881100091911572051060774309367007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-28875532817974944494809986434907474800000000000000)
      constant := (259562262481473207502512837627937052754936764482308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136719692929691699943/50000000000000000000)
  centralHi := (273439385859383399887/100000000000000000000)
  directionLo := (277959351339595434931/100000000000000000000)
  directionHi := (69489837834898858733/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree032.table
  base := (-6313037185206820789170473670228730335591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-14831348122518250069275513684092362400000000000000)
      constant := (137200376290663703463754663913138798684448764108004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree032.table
  base := (-12635565853293651885065397401294456492859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-29690307537255961028409089925584724800000000000000)
      constant := (274926747707347414653322542256361542929881285243796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277959351339595434931/100000000000000000000)
  centralHi := (69489837834898858733/25000000000000000000)
  directionLo := (282406983368153533677/100000000000000000000)
  directionHi := (141203491684076766839/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree033.table
  base := (-6370593710921287037694133142565624405953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-15238304055717829259671033201971612400000000000000)
      constant := (145097705874262248305356654883578197151302357047932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree033.table
  base := (-12749892191460948233843465817406679635247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-30505082256536977562008193416261974800000000000000)
      constant := (290753405215031233749847022161442588008517215164868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282406983368153533677/100000000000000000000)
  centralHi := (141203491684076766839/50000000000000000000)
  directionLo := (286785647327533528137/100000000000000000000)
  directionHi := (143392823663766764069/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree034.table
  base := (-3198851425489658819638330799754921251797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-15645259988917408450066552719850862400000000000000)
      constant := (153224807100841698580093717408749457384120214786136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree034.table
  base := (-200052876995479952259514538978181986911/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-31319856975817994095607296906939224800000000000000)
      constant := (307040486056520889132354488428895370713383846789376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286785647327533528137/100000000000000000000)
  centralHi := (143392823663766764069/50000000000000000000)
  directionLo := (291098455459736733297/100000000000000000000)
  directionHi := (145549227729868366649/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree035.table
  base := (-6395911968102113300345372762826215570961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-16052215922116987640462072237730112400000000000000)
      constant := (161580905920837210248716896009906187639567096404284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree035.table
  base := (-12799132470291240111873476450537697119027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-32134631695099010629206400397616474800000000000000)
      constant := (323786444092215872225375016927373661542230844811188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291098455459736733297/100000000000000000000)
  centralHi := (145549227729868366649/50000000000000000000)
  directionLo := (73837073186939864829/25000000000000000000)
  directionHi := (295348292747759459317/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree036.table
  base := (-509327195140422626739549779125863944269/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-16459171855316566830857591755609362400000000000000)
      constant := (170165317570033491676143349773775395822309719072950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree036.table
  base := (-3184967797548422224510476533207628153107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-32949406414380027162805503888293724800000000000000)
      constant := (340989911686055796272581085235895392676326797082832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73837073186939864829/25000000000000000000)
  centralHi := (295348292747759459317/100000000000000000000)
  directionLo := (299537839491086860099/100000000000000000000)
  directionHi := (2995378394910868601/1000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree037.table
  base := (-12621896818066761084094570883606986833823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-16866127788516146021253111273488612400000000000000)
      constant := (178977435937815164570072999717971974799464735407106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree037.table
  base := (-12628019947836386205328020193925066002079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-33764181133661043696404607378970974800000000000000)
      constant := (358649678432058785320421273841091025215954909289476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299537839491086860099/100000000000000000000)
  centralHi := (2995378394910868601/1000000000000000000)
  directionLo := (303669591077144250487/100000000000000000000)
  directionHi := (37958698884643031311/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree038.table
  base := (-2492024165262792268170315887316599188927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-17273083721715725211648630791367862400000000000000)
      constant := (188016724250986653882204566163203726442149749216970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree038.table
  base := (-6232860676697937871496598280533357944339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-34578955852942060230003710869648224800000000000000)
      constant := (376764672515289620344630012778891824264214993737832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303669591077144250487/100000000000000000000)
  centralHi := (37958698884643031311/12500000000000000000)
  directionLo := (30774587536298825117/10000000000000000000)
  directionHi := (307745875362988251171/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree039.table
  base := (-3062438356345720623562933975372812166773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-17680039654915304402044150309247112400000000000000)
      constant := (197282706902775980530330207345263776307443086728024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree039.table
  base := (-12254873643298795337158647303024325948469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-35393730572223076763602814360325474800000000000000)
      constant := (395333944365838235295116143515774322019260106110636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30774587536298825117/10000000000000000000)
  centralHi := (307745875362988251171/100000000000000000000)
  directionLo := (311768868011069686333/100000000000000000000)
  directionHi := (155884434005534843167/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree040.table
  base := (-11992480265710190539491366629857194546059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-18086995588114883592439669827126362400000000000000)
      constant := (206774962280018660362004065207754110214192548992298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree040.table
  base := (-5998579680850508895289704025482054786611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-36208505291504093297201917851002724800000000000000)
      constant := (414356652311255216615633495858896761997731394385768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311768868011069686333/100000000000000000000)
  centralHi := (155884434005534843167/50000000000000000000)
  directionLo := (157870303032960954689/50000000000000000000)
  directionHi := (315740606065921909379/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree041.table
  base := (-11689796321104522329183783606806918358001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-18493951521314462782835189345005612400000000000000)
      constant := (216493116461393540360077361527759840636967351757022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree041.table
  base := (-11694070556131985477178964988239250722223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-37023280010785109830801021341679974800000000000000)
      constant := (433832049972734181203230797379504306229743642703812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157870303032960954689/50000000000000000000)
  centralHi := (315740606065921909379/100000000000000000000)
  directionLo := (79915750003068690823/25000000000000000000)
  directionHi := (319663000012274763293/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree042.table
  base := (-11343028041616904433230769518632739244327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-18900907454514041973230708862884862400000000000000)
      constant := (226436837676569489711035416859407438102868438462194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree042.table
  base := (-3545915915126951854296298682239679527/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-37838054730066126364400124832357224800000000000000)
      constant := (453759475184385066307038964642870140076219114201600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79915750003068690823/25000000000000000000)
  centralHi := (319663000012274763293/100000000000000000000)
  directionLo := (323537844517174632483/100000000000000000000)
  directionHi := (80884461129293658121/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree043.table
  base := (-342292276446924136215509242463009485601/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-19307863387713621163626228380764112400000000000000)
      constant := (236605831430695985303230055101538037369029509255104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree043.table
  base := (-5478457661749574633923282063371714074859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-38652829449347142897999228323034474800000000000000)
      constant := (474138340244158785918868011355199415215952205703592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323537844517174632483/100000000000000000000)
  centralHi := (80884461129293658121/25000000000000000000)
  directionLo := (163683414013753512831/50000000000000000000)
  directionHi := (327366828027507025663/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree044.table
  base := (-10521816287821456965219368254326624940687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-19714819320913200354021747898643362400000000000000)
      constant := (246999836211209529691713778029562206091646056942114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree044.table
  base := (-10525066888837298389077292785848883853897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-39467604168628159431598331813711724800000000000000)
      constant := (494968123330118849539194428617129999816045162085468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163683414013753512831/50000000000000000000)
  centralHi := (327366828027507025663/100000000000000000000)
  directionLo := (331151541368545122403/100000000000000000000)
  directionHi := (82787885342136280601/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree045.table
  base := (-10049347177630025898228990677595471103903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-20121775254112779544417267416522612400000000000000)
      constant := (257618619704738626854305745486573063770063249828866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree045.table
  base := (-2513078048284055542801713296828845728097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-40282378887909175965197435304388974800000000000000)
      constant := (516248360937424907458746274731252789974549699801072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331151541368545122403/100000000000000000000)
  centralHi := (82787885342136280601/25000000000000000000)
  directionLo := (10465421420867050479/3125000000000000000)
  directionHi := (334893485467745615329/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree046.table
  base := (-1907354184626513967646699477140613347703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-20528731187312358734812786934401862400000000000000)
      constant := (268461975461226631854254312158295417535896834962330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree046.table
  base := (-1907894911302006918655340473554399604297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-41097153607190192498796538795066224800000000000000)
      constant := (537978641210105941613896824390302641235696299515340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10465421420867050479/3125000000000000000)
  centralHi := (334893485467745615329/100000000000000000000)
  directionLo := (338594078310160403373/100000000000000000000)
  directionHi := (169297039155080201687/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree047.table
  base := (-8984821295946146570305388349753782041619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-20935687120511937925208306452281112400000000000000)
      constant := (279529719950466600790990200696051612784115502254618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree047.table
  base := (-2246821452807196463116148152225909910927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-41911928326471209032395642285743474800000000000000)
      constant := (560158598057883047253992481824215157753670941819152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338594078310160403373/100000000000000000000)
  centralHi := (169297039155080201687/50000000000000000000)
  directionLo := (8556366530421913259/2500000000000000000)
  directionHi := (342254661216876530361/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree048.table
  base := (-4197075411210984338955330829508321705129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-21342643053711517115603825970160362400000000000000)
      constant := (290821689963234450304076155960003727865235834323676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree048.table
  base := (-524774792780643207476044342428710100101/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-42726703045752225565994745776420724800000000000000)
      constant := (582787905962312875610255769173982758140942725863104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8556366530421913259/2500000000000000000)
  centralHi := (342254661216876530361/100000000000000000000)
  directionLo := (345876504525315827187/100000000000000000000)
  directionHi := (86469126131328956797/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree049.table
  base := (-7765339963359514456149145497002371160477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-21749598986911096305999345488039612400000000000000)
      constant := (302337740315268245819408626516916464961764818767494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree049.table
  base := (-7767385970294964643499247793860403449383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-43541477765033242099593849267097974800000000000000)
      constant := (605866275388667714695873383222841133879145298618852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345876504525315827187/100000000000000000000)
  centralHi := (86469126131328956797/25000000000000000000)
  directionLo := (174730406369800668391/50000000000000000000)
  directionHi := (349460812739601336783/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree050.table
  base := (-7098905228810715374660012187807139119273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-22156554920110675496394865005918862400000000000000)
      constant := (314077741817601671510875424556321004302383617137006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree050.table
  base := (-142015372728911586020892962878346180071/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-44356252484314258633192952757775224800000000000000)
      constant := (629393448730506499295613626739951976511043751256200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174730406369800668391/50000000000000000000)
  centralHi := (349460812739601336783/100000000000000000000)
  directionLo := (44126091151273989637/12500000000000000000)
  directionHi := (353008729210191917097/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree051.table
  base := (-6395306355603425737477132955045711277313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-22563510853310254686790384523798112400000000000000)
      constant := (326041579481329195498018696930383211652035397853886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree051.table
  base := (-799625374299466969681186336229399834847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-45171027203595275166792056248452474800000000000000)
      constant := (653369196723044468923925913327483981286075193178144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44126091151273989637/12500000000000000000)
  centralHi := (353008729210191917097/100000000000000000000)
  directionLo := (356521340394325478483/100000000000000000000)
  directionHi := (89130335098581369621/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree052.table
  base := (-113099053186558268252596739734295280019/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-22970466786509833877185904041677362400000000000000)
      constant := (338229150928853700514940708948575788450571194970900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree052.table
  base := (-353531065235115567636026337066178391989/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-45985801922876291700391159739129724800000000000000)
      constant := (677793315269387459322414650951332355751360893848256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356521340394325478483/100000000000000000000)
  centralHi := (89130335098581369621/25000000000000000000)
  directionLo := (179999839871135988329/50000000000000000000)
  directionHi := (359999679742271976659/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree053.table
  base := (-304888041169012742931591485648458328331/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47192260000000000000000000000000000000000000000
      center := (315963427)
      previous := (0)
      next := (283378275)
      square := (7282478322882809700063999514250000000000000000)
      linear := (-441083447541687039010970255840690800000000000000)
      constant := (6615855943153310790919853938772281597552380931104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree053.table
  base := (-975922817893719582530448536429069678541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94384520000000000000000000000000000000000000000
      center := (632596779)
      previous := (0)
      next := (566086625)
      square := (14564956645765619400127999028500000000000000000)
      linear := (-883029747965232230830004966600131600000000000000)
      constant := (13257841936426840462557294167264525922172176707340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179999839871135988329/50000000000000000000)
  centralHi := (359999679742271976659/100000000000000000000)
  directionLo := (72688946249759400481/20000000000000000000)
  directionHi := (181722365624398501203/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree054.table
  base := (-2032699529101765477057106296868118159449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-23784378652908992257976943077435862400000000000000)
      constant := (363275140441394012682546476577630562970350750153756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree054.table
  base := (-2033338858718974236060494638033061310453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-47615351361438324767589366720484224800000000000000)
      constant := (727985956936789529744275097451535227299272619691864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72688946249759400481/20000000000000000000)
  centralHi := (181722365624398501203/50000000000000000000)
  directionLo := (366857432704425619857/100000000000000000000)
  directionHi := (183428716352212809929/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree055.table
  base := (-3216813164294770021171982536179926328941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-24191334586108571448372462595315112400000000000000)
      constant := (376133404930620998900736223606988423302489985257702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree055.table
  base := (-402247025527161448320749208504222443263/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-48430126080719341301188470211161474800000000000000)
      constant := (753754173981017585484707116774405359830902327276576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366857432704425619857/100000000000000000000)
  centralHi := (183428716352212809929/50000000000000000000)
  directionLo := (74047735735390063161/20000000000000000000)
  directionHi := (185119339338475157903/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree056.table
  base := (-291588600190102041928210246283064579857/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-24598290519308150638767982113194362400000000000000)
      constant := (389215093967995258296894033909400627108625342190832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree056.table
  base := (-2333766426766615647505775694616748258887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-49244900800000357834787573701838724800000000000000)
      constant := (779970145263701303650075696734439826447607808285028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74047735735390063161/20000000000000000000)
  centralHi := (185119339338475157903/50000000000000000000)
  directionLo := (93397330812511030149/25000000000000000000)
  directionHi := (373589323250044120597/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree057.table
  base := (-706657893301614907777442859460653820233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-25005246452507729829163501631073612400000000000000)
      constant := (402520150071993266993594009120681066570543052636252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree057.table
  base := (-1414277330610337844357760747385704535539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-50059675519281374368386677192515974800000000000000)
      constant := (806633756257599514437455399622976812669522041281716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93397330812511030149/25000000000000000000)
  centralHi := (373589323250044120597/100000000000000000000)
  directionLo := (376910182542735038551/100000000000000000000)
  directionHi := (47113772817841879819/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree058.table
  base := (-114709752943337073999254439006374618387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-25412202385707309019559021148952862400000000000000)
      constant := (416048521995179522632113927551531378179855614206056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree058.table
  base := (-18388520302132075217700479221854448361/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-50874450238562390901985780683193224800000000000000)
      constant := (833744904868244926481797676514987539905559645247100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376910182542735038551/100000000000000000000)
  centralHi := (47113772817841879819/12500000000000000000)
  directionLo := (380202037030799902961/100000000000000000000)
  directionHi := (190101018515399951481/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree059.table
  base := (530538817597337425353914581420756366991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-25819158318906888209954540666832112400000000000000)
      constant := (429800164039473232823748135534496081470498781855198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree059.table
  base := (529744571969595693172662587359196533803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-51689224957843407435584884173870474800000000000000)
      constant := (861303500067119134701325167628854105361871897626668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380202037030799902961/100000000000000000000)
  centralHi := (190101018515399951481/50000000000000000000)
  directionLo := (191732816844392624683/50000000000000000000)
  directionHi := (383465633688785249367/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree060.table
  base := (1554654751359294332038922489731875948307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-26226114252106467400350060184711362400000000000000)
      constant := (443775035447949531423242653611083896306213327670246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree060.table
  base := (776966566104382419073567118192089313981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-52503999677124423969183987664547724800000000000000)
      constant := (889309460677732855807420395221955430347590595325672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191732816844392624683/50000000000000000000)
  centralHi := (383465633688785249367/100000000000000000000)
  directionLo := (48337710996163738761/12500000000000000000)
  directionHi := (386701687969309910089/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree061.table
  base := (522672686786676726468782314763942701873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-26633070185306046590745579702590612400000000000000)
      constant := (457973099864419517637893797622999847199215167228970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree061.table
  base := (163294246005226007339964913019538899801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-53318774396405440502783091155224974800000000000000)
      constant := (917762714297104738332822546476490709886783056748096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48337710996163738761/12500000000000000000)
  centralHi := (386701687969309910089/100000000000000000000)
  directionLo := (97477721408626692203/25000000000000000000)
  directionHi := (389910885634506768813/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree062.table
  base := (1853267591882134444934519182506445324537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-27040026118505625781141099220469862400000000000000)
      constant := (472394324853065105267783076722499873965972145526372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree062.table
  base := (3705939868964665837986329284893108209907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-54133549115686457036382194645902224800000000000000)
      constant := (946663196337196439657578331625469532729410696630092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97477721408626692203/25000000000000000000)
  centralHi := (389910885634506768813/100000000000000000000)
  directionLo := (196546942226441994713/50000000000000000000)
  directionHi := (393093884452883989427/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree063.table
  base := (1208513571404680415572284486200973281237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-27446982051705204971536618738349112400000000000000)
      constant := (487038681471310420183275588716485423858833220063144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree063.table
  base := (4833513735006749503393683092179833237949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-54948323834967473569981298136579474800000000000000)
      constant := (976010849172673835001527785121945018013372469392244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196546942226441994713/50000000000000000000)
  centralHi := (393093884452883989427/100000000000000000000)
  directionLo := (198125657886749489713/50000000000000000000)
  directionHi := (396251315773498979427/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree064.table
  base := (2997908735825223725253966837383302694181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-27853937984904784161932138256228362400000000000000)
      constant := (501906143889907286943170350968548081328266396534036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree064.table
  base := (119906534839372290800756568560989200773/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-55763098554248490103580401627256724800000000000000)
      constant := (1005805621382956267518361661970455742156637956999400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198125657886749489713/50000000000000000000)
  centralHi := (396251315773498979427/100000000000000000000)
  directionLo := (199691892994057906733/50000000000000000000)
  directionHi := (399383785988115813467/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree065.table
  base := (898966571243831692113877759549665273883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-28260893918104363352327657774107612400000000000000)
      constant := (516996689054912078003723806282564854648365648412592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree065.table
  base := (3595643576626134618955592357179172769839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-56577873273529506637179505117933974800000000000000)
      constant := (1036047467077915467441360825318085830874310239618168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199691892994057906733/50000000000000000000)
  centralHi := (399383785988115813467/100000000000000000000)
  directionLo := (201245938945468527719/50000000000000000000)
  directionHi := (402491877890937055439/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree066.table
  base := (4210858650882635129560505824630112667811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-28667849851303942542723177291986862400000000000000)
      constant := (532310296386846914347641316446140850416995481634316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree066.table
  base := (8421313088357370122182102760884818378057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-57392647992810523170778608608611224800000000000000)
      constant := (1066736345297817306693377553529809740096870468931492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201245938945468527719/50000000000000000000)
  centralHi := (402491877890937055439/100000000000000000000)
  directionLo := (405576151944545276587/100000000000000000000)
  directionHi := (101394037986136319147/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree067.table
  base := (4842849105363705190453520582190642491253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-29074805784503521733118696809866112400000000000000)
      constant := (547846947512880382546355573876625260302151148598868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree067.table
  base := (9685331455113589944377507399125788640369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-58207422712091539704377712099288474800000000000000)
      constant := (1097872219479183901167784571362301128546346207645764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405576151944545276587/100000000000000000000)
  centralHi := (101394037986136319147/25000000000000000000)
  directionLo := (408637147459842139863/100000000000000000000)
  directionHi := (51079643432480267483/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree068.table
  base := (549180485468187920865351300339740779127/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-29481761717703100923514216327745362400000000000000)
      constant := (563606626028340687328496287601373343529203379444120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree068.table
  base := (5491638499481912922829642938902062514529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-59022197431372556237976815589965724800000000000000)
      constant := (1129455056979208986045194944757963587672904414525448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408637147459842139863/100000000000000000000)
  centralHi := (51079643432480267483/12500000000000000000)
  directionLo := (51459422962127503203/12500000000000000000)
  directionHi := (658680613915232041/160000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree069.table
  base := (12315393229817868622188438578784941465059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-29888717650902680113909735845624612400000000000000)
      constant := (579589317284295430833328342365087610141030379789702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree069.table
  base := (2463018291251013941935034122570153138877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-59836972150653572771575919080642974800000000000000)
      constant := (1161484828652201871452233205204577351813994073077060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51459422962127503203/12500000000000000000)
  centralHi := (658680613915232041/160000000000000000)
  directionLo := (132701235486057931/32000000000000000)
  directionHi := (51836420111741379297/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree070.table
  base := (1710124558402436193088168207888043675383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-30295673584102259304305255363503862400000000000000)
      constant := (595795008198303921345363136116013910180049277748592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree070.table
  base := (13680722799979477190641361547366176331569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-60651746869934589305175022571320224800000000000000)
      constant := (1193961508472278496537398307343766314231639654832964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132701235486057931/32000000000000000)
  centralHi := (51836420111741379297/12500000000000000000)
  directionLo := (407896055886348299/97656250000000000)
  directionHi := (417685561227620658177/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree071.table
  base := (1508037270544116862986308093554665298841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-30702629517301838494700774881383112400000000000000)
      constant := (612223687085776104313801914117690725616781755044980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree071.table
  base := (15080124567719810084646731945653781844151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-61466521589215605838774126061997474800000000000000)
      constant := (1226885073197174231242400637931608667963388006795356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407896055886348299/97656250000000000)
  centralHi := (417685561227620658177/100000000000000000000)
  directionLo := (420658449714259677491/100000000000000000000)
  directionHi := (105164612428564919373/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree072.table
  base := (16513480216142606312715832197297835906813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-31109585450501417685096294399262362400000000000000)
      constant := (628875343509662150375246585197570761878623770797114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree072.table
  base := (16513255262712094964870986984325297136789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-62281296308496622372373229552674724800000000000000)
      constant := (1260255502068632684885769297106335276278799981763284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420658449714259677491/100000000000000000000)
  centralHi := (105164612428564919373/25000000000000000000)
  directionLo := (84722095010446060103/20000000000000000000)
  directionHi := (105902618763057575129/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree073.table
  base := (17980281723027953461828918179027188930931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-31516541383700996875491813917141612400000000000000)
      constant := (645749968146453038119300519202813279229617374308518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree073.table
  base := (17980077819962485259803277073431269498203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-63096071027777638905972333043351974800000000000000)
      constant := (1294072776545337096505994089637246386810266214393068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84722095010446060103/20000000000000000000)
  centralHi := (105902618763057575129/25000000000000000000)
  directionLo := (426542070412694604467/100000000000000000000)
  directionHi := (106635517603173651117/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree074.table
  base := (243509299051844992529951506916209475667/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-31923497316900576065887333435020862400000000000000)
      constant := (662847552666699165516483294457314627255019672666080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree074.table
  base := (19480559130261069039028923381147879371021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-63910845747058655439571436534029224800000000000000)
      constant := (1328336880064803974984064362353113984310294110673076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426542070412694604467/100000000000000000000)
  centralHi := (106635517603173651117/25000000000000000000)
  directionLo := (107363413545397302043/25000000000000000000)
  directionHi := (429453654181589208173/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree075.table
  base := (21014837065878094082289975985110517683257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-32330453250100155256282852952900112400000000000000)
      constant := (680168089628454643442922743105993128399987168551346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree075.table
  base := (4202933923147371196643487293414602426961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-64725620466339671973170540024706474800000000000000)
      constant := (1363047797831059593290942443927791731143078049658580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107363413545397302043/25000000000000000000)
  centralHi := (429453654181589208173/100000000000000000000)
  directionLo := (27021601916040298999/6250000000000000000)
  directionHi := (86469126131328956797/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree076.table
  base := (22582534562924054771523712656650499774229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-32737409183299734446678372470779362400000000000000)
      constant := (697711572382232560942075723828256950306719388217962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree076.table
  base := (22582382851307780761906539662961843557129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-65540395185620688506769643515383724800000000000000)
      constant := (1398205516625274911933459420545650346327009980188324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27021601916040298999/6250000000000000000)
  centralHi := (86469126131328956797/20000000000000000000)
  directionLo := (217609195351359060019/50000000000000000000)
  directionHi := (435218390702718120039/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree077.table
  base := (2418381265931507108517773644045303191099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-33144365116499313637073891988658612400000000000000)
      constant := (715477994986213877570225561128770077498578205768220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree077.table
  base := (12091837613504064639932121474370726892577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-66355169904901705040368747006060974800000000000000)
      constant := (1433810024636848940862536052173236153463953900105224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609195351359060019/50000000000000000000)
  centralHi := (435218390702718120039/100000000000000000000)
  directionLo := (438072312368444132681/100000000000000000000)
  directionHi := (219036156184222066341/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree078.table
  base := (516373002518565230453232787804107918987/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-33551321049698892827469411506537862400000000000000)
      constant := (733467352130592074370029475775397694044936761764300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree078.table
  base := (25818525646732853659287212552883064377339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-67169944624182721573967850496738224800000000000000)
      constant := (1469861311312709211366497861354693825431136474079084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438072312368444132681/100000000000000000000)
  centralHi := (219036156184222066341/50000000000000000000)
  directionLo := (88181552293392427513/20000000000000000000)
  directionHi := (220453880733481068783/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree079.table
  base := (27487027990561611737104370738245825100829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-33958276982898472017864931024417112400000000000000)
      constant := (751679639070059373103506743052346123386986096432762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree079.table
  base := (27486915259432156936816401617590102229733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-67984719343463738107566953987415474800000000000000)
      constant := (1506359367222845104558179111595770981835232678345748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88181552293392427513/20000000000000000000)
  centralHi := (220453880733481068783/50000000000000000000)
  directionLo := (11093127303081046473/2500000000000000000)
  directionHi := (443725092123241858921/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree080.table
  base := (5837785859404377927498359614211681127343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-34365232916098051208260450542296362400000000000000)
      constant := (770114851563550051789536105176790091796164595077270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree080.table
  base := (2918882721922785236439794820346195534369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-68799494062744754641166057478092724800000000000000)
      constant := (1543304183940308949273747052021995664664890763097640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11093127303081046473/2500000000000000000)
  centralHi := (443725092123241858921/100000000000000000000)
  directionLo := (3488473806955683493/781250000000000000)
  directionHi := (89304929458065497421/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree081.table
  base := (15462169445040125611152688580089426294803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-34772188849297630398655970060175612400000000000000)
      constant := (788772985820453760610336313418258313806924906142668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree081.table
  base := (30924246471311802921954380037932208706681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-69614268782025771174765160968769974800000000000000)
      constant := (1580695753934114295078110196942092575599995506984036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/781250000000000000)
  centralHi := (89304929458065497421/20000000000000000000)
  directionLo := (449306759236630290149/100000000000000000000)
  directionHi := (8986135184732605803/2000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree082.table
  base := (1307729728939772643138439090901465221581/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-35179144782497209589051489578054862400000000000000)
      constant := (807654038452598199636699547169776796298109581605450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree082.table
  base := (4086644945103989722249174985537488739207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-70429043501306787708364264459447224800000000000000)
      constant := (1618534070473633433771396499156629982026191413927136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449306759236630290149/100000000000000000000)
  centralHi := (8986135184732605803/2000000000000000000)
  directionLo := (452071750006229819307/100000000000000000000)
  directionHi := (113017937501557454827/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree083.table
  base := (34495630188602517496640656384652395016609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-35586100715696788779447009095934112400000000000000)
      constant := (826758006431377312855412379695369633626806536105602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree083.table
  base := (34495554462277739421190835148629454485177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-71243818220587804241963367950124474800000000000000)
      constant := (1656819127543249594231516307713826319163059974778212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452071750006229819307/100000000000000000000)
  centralHi := (113017937501557454827/25000000000000000000)
  directionLo := (227409965926994414733/50000000000000000000)
  directionHi := (454819931853988829467/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree084.table
  base := (36331488961269339993789599724196982267357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-35993056648896367969842528613813362400000000000000)
      constant := (846084887049469387400349964406202552675395455601146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree084.table
  base := (7266284085430003826126795800474674655747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-72058592939868820775562471440801724800000000000000)
      constant := (1695550919766155482210784635695341758597779414665660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227409965926994414733/50000000000000000000)
  centralHi := (454819931853988829467/100000000000000000000)
  directionLo := (457551607657146075069/100000000000000000000)
  directionHi := (45755160765714607507/10000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree085.table
  base := (7640161973040509311588208714432864264339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-36400012582095947160238048131692612400000000000000)
      constant := (865634677886650098120745400590910275797045962627710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree085.table
  base := (7640149569588149824691286135016299223333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-72873367659149837309161574931478974800000000000000)
      constant := (1734729442336310929642268302958689482000822437136740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457551607657146075069/100000000000000000000)
  centralHi := (45755160765714607507/10000000000000000000)
  directionLo := (460267071304922732331/100000000000000000000)
  directionHi := (115066767826230683083/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree086.table
  base := (40103584249879111630548936226759387350089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-36806968515295526350633567649571862400000000000000)
      constant := (885407376779259466698427270631904670615910388889042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree086.table
  base := (20051764068332669619322920937823611391583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-73688142378430853842760678422156224800000000000000)
      constant := (1774354690957680078984324781503966230702127591048696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460267071304922732331/100000000000000000000)
  centralHi := (115066767826230683083/25000000000000000000)
  directionLo := (462966608067561087421/100000000000000000000)
  directionHi := (231483304033780543711/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree087.table
  base := (42039804381508354364418863742135926794347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-37213924448495105541029087167451112400000000000000)
      constant := (905402981792929671973971133545741724846884887817366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree087.table
  base := (42039753616380034453074914370122082710823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-74502917097711870376359781912833474800000000000000)
      constant := (1814426661789964277897220138934819211975725036597788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462966608067561087421/100000000000000000000)
  centralHi := (231483304033780543711/50000000000000000000)
  directionLo := (232825247473053602163/50000000000000000000)
  directionHi := (465650494946107204327/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree088.table
  base := (44009463345631397362684443102769669709099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-37620880381694684731424606685330362400000000000000)
      constant := (925621491198223326109845469210021949957037399180822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree088.table
  base := (44009417424287953464321558969708147533267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-75317691816992886909958885403510724800000000000000)
      constant := (1854945351400132042035056131506194452038587926082252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232825247473053602163/50000000000000000000)
  centralHi := (465650494946107204327/100000000000000000000)
  directionLo := (234159500502075776399/50000000000000000000)
  directionHi := (468319001004151552799/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree089.table
  base := (23006277480053967670900295090757627673959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-38027836314894263921820126203209612400000000000000)
      constant := (946062903448869814095921980965939726259030284587804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree089.table
  base := (46012513425188663586997643028973364390159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-76132466536273903443557988894187974800000000000000)
      constant := (1895910756719123247300978608676884148030976324675004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234159500502075776399/50000000000000000000)
  centralHi := (468319001004151552799/100000000000000000000)
  directionLo := (470972387682652150617/100000000000000000000)
  directionHi := (235486193841326075309/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree090.table
  base := (48049073697376488636657773304785591813747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-38434792248093843112215645721088862400000000000000)
      constant := (966727217162321107806195690493238820733579565990566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree090.table
  base := (48049036134161095028097802386044313361913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-76947241255554919977157092384865224800000000000000)
      constant := (1937322875003172188920401223981517087241586847369828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470972387682652150617/100000000000000000000)
  centralHi := (235486193841326075309/50000000000000000000)
  directionLo := (473610909098882864067/100000000000000000000)
  directionHi := (118402727274720716017/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree091.table
  base := (50119014614994699620514879885851257882553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-38841748181293422302611165238968112400000000000000)
      constant := (987614431102378575927155605241143534181598600390834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree091.table
  base := (5011898064748969868670837950804100274499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-77762015974835936510756195875542474800000000000000)
      constant := (1979181703799254223805665291643361379827344186840440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473610909098882864067/100000000000000000000)
  centralHi := (118402727274720716017/25000000000000000000)
  directionLo := (476234812330474408129/100000000000000000000)
  directionHi := (47623481233047440813/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree092.table
  base := (26111186646786727342562690316811043891671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-39248704114493001493006684756847362400000000000000)
      constant := (1008724544163669129978781210931319329834595786464476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree092.table
  base := (52222342580950713685067140127077929174431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-78576790694116953044355299366219724800000000000000)
      constant := (2021487240914214219168646265738256825142930130903036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476234812330474408129/100000000000000000000)
  centralHi := (47623481233047440813/10000000000000000000)
  directionLo := (478844337685446659017/100000000000000000000)
  directionHi := (239422168842723329509/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree093.table
  base := (1698723305666066921225148563642999388717/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-39655660047692580683402204274726612400000000000000)
      constant := (1030057555357772939777951046056085284546736664679232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree093.table
  base := (54359118014670693913337679971780246428273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-79391565413397969577954402856896974800000000000000)
      constant := (2064239484387182694548683431899101200804455586129988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478844337685446659017/100000000000000000000)
  centralHi := (239422168842723329509/50000000000000000000)
  directionLo := (481439718959067567627/100000000000000000000)
  directionHi := (120359929739766891907/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree094.table
  base := (56529328544443475998372078964301816061131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-40062615980892159873797723792605862400000000000000)
      constant := (1051613463800826243045785607099604364316754071244118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree094.table
  base := (56529303443854341293655580478630594339059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-80206340132678986111553506347574224800000000000000)
      constant := (2107438432464928013836895164538552126391236045123404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481439718959067567627/100000000000000000000)
  centralHi := (120359929739766891907/25000000000000000000)
  directionLo := (96804236735663146409/20000000000000000000)
  directionHi := (242010591839157866023/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree095.table
  base := (29366459211458102916257318700250860992217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-40469571914091739064193243310485112400000000000000)
      constant := (1073392268702441750815715464166837957889986763988452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree095.table
  base := (58732895734754355200991336885488307088177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-81021114851960002645152609838251474800000000000000)
      constant := (2151084083579830832748099181754704089049689974246212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804236735663146409/20000000000000000000)
  centralHi := (242010591839157866023/50000000000000000000)
  directionLo := (243294476667335045609/50000000000000000000)
  directionHi := (486588953334670091219/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree096.table
  base := (15242478147705908495487800899877918692553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-40876527847291318254588762828364362400000000000000)
      constant := (1095393969355806067872868682748493291792593810283336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree096.table
  base := (7621236510665431387675053856906014696371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-81835889571241019178751713328928724800000000000000)
      constant := (2195176436330200745051684665077199031006548717261408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243294476667335045609/50000000000000000000)
  centralHi := (486588953334670091219/100000000000000000000)
  directionLo := (489143243605900826477/100000000000000000000)
  directionHi := (244571621802950413239/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree097.table
  base := (63240308521006217275166943159829448558897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-41283483780490897444984282346243612400000000000000)
      constant := (1117618565128828632036239093752227387627854890447266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree097.table
  base := (63240289990048831141860054848436533777753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-82650664290522035712350816819605974800000000000000)
      constant := (2239715489462685150017814296841109343302708118992868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489143243605900826477/100000000000000000000)
  centralHi := (244571621802950413239/50000000000000000000)
  directionLo := (49168426456749003007/10000000000000000000)
  directionHi := (491684264567490030071/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree098.table
  base := (65544103953422278396882983567269301021641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-41690439713690476635379801864122862400000000000000)
      constant := (1140066055456230128738323361799799817022307202802898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree098.table
  base := (16386021802130752014653739691628340370323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-83465439009803052245949920310283224800000000000000)
      constant := (2284701241856547185610571117852872480594090642319152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49168426456749003007/10000000000000000000)
  centralHi := (491684264567490030071/100000000000000000000)
  directionLo := (98842444178853736787/20000000000000000000)
  directionHi := (15444131902945896373/3125000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree099.table
  base := (67881296866872845024262210734969032317379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-42097395646890055825775321382002112400000000000000)
      constant := (1162736439832470336687083181855335203324871807118662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree099.table
  base := (67881281737352704628263562373610936486977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-84280213729084068779549023800960474800000000000000)
      constant := (2330133692509613493767579366248128004657491195099012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98842444178853736787/20000000000000000000)
  centralHi := (15444131902945896373/3125000000000000000)
  directionLo := (124181828013204420901/25000000000000000000)
  directionHi := (99345462410563536721/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree100.table
  base := (70251885453725428284087083037325792013603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-42504351580089635016170840899881362400000000000000)
      constant := (1185629717805426065165953010835765302951482944457734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree100.table
  base := (878148397313127597840282849399849121897/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-85094988448365085313148127291637724800000000000000)
      constant := (2376012840525713922726807183395090888115692009802560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124181828013204420901/25000000000000000000)
  centralHi := (99345462410563536721/20000000000000000000)
  directionLo := (31201858280321547927/6250000000000000000)
  directionHi := (499229732485144766833/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree101.table
  base := (36327934048658869992276453017749775625631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-42911307513289214206566360417760612400000000000000)
      constant := (1208745888970739394881257190592445164378424272650236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree101.table
  base := (72655855749589613378015085019034405174271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-85909763167646101846747230782314974800000000000000)
      constant := (2422338685103454308673437782718672402988053148830076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31201858280321547927/6250000000000000000)
  centralHi := (499229732485144766833/100000000000000000000)
  directionLo := (50171967178411601541/10000000000000000000)
  directionHi := (501719671784116015411/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree102.table
  base := (75093243351756425704775181974778143196687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-43318263446488793396961879935639862400000000000000)
      constant := (1232084952966764957728252308690922885753093005425886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree102.table
  base := (75093232198344353537063242466419941396811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-86724537886927118380346334272992224800000000000000)
      constant := (2469111225526180465648128327891641964721980519558316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50171967178411601541/10000000000000000000)
  centralHi := (501719671784116015411/100000000000000000000)
  directionLo := (252098657430544933203/50000000000000000000)
  directionHi := (504197314861089866407/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree103.table
  base := (77564009923856305317139464043068612234213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-43725219379688372587357399453519112400000000000000)
      constant := (1255646909470052598088673530116522418975899652194314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree103.table
  base := (77563999850152704563135165253514508903909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-87539312606208134913945437763669474800000000000000)
      constant := (2516330461153006671661128282807350030400435238570004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252098657430544933203/50000000000000000000)
  centralHi := (504197314861089866407/100000000000000000000)
  directionLo := (506662842106173091257/100000000000000000000)
  directionHi := (253331421053086545629/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree104.table
  base := (80068166656992761188534055470819462460417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-44132175312887951777752918971398362400000000000000)
      constant := (1279431758191308548670486178313397642373108865493826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree104.table
  base := (5004259847455313557923325472362805063757/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-88354087325489151447544541254346724800000000000000)
      constant := (2563996391410795468703225392930970644728324021771072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506662842106173091257/100000000000000000000)
  centralHi := (253331421053086545629/50000000000000000000)
  directionLo := (101823285908298358433/20000000000000000000)
  directionHi := (254558214770745896083/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree105.table
  base := (41302856258332075413710633021471031190677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-44539131246087530968148438489277612400000000000000)
      constant := (1303439498871784315914385472556469987256036508736212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree105.table
  base := (82605704301110554002769461789613276276089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-89168862044770167981143644745023974800000000000000)
      constant := (2612109015786987671430251316494806507604814053034084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101823285908298358433/20000000000000000000)
  centralHi := (254558214770745896083/50000000000000000000)
  directionLo := (255779124483922978189/50000000000000000000)
  directionHi := (511558248967845956379/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree106.table
  base := (10647080822197845002459660753713817026731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47192260000000000000000000000000000000000000000
      center := (315963427)
      previous := (0)
      next := (283378275)
      square := (7282478322882809700063999514250000000000000000)
      linear := (-848039380741266229406489773719940800000000000000)
      constant := (25050379835472601554437333818691961534974333041648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree106.table
  base := (85176639159283378027292065008902253261493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94384520000000000000000000000000000000000000000
      center := (632596779)
      previous := (0)
      next := (566086625)
      square := (14564956645765619400127999028500000000000000000)
      linear := (-1697804467246248764429108457277381600000000000000)
      constant := (50201289317418721904647614936869078090100445128836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255779124483922978189/50000000000000000000)
  centralHi := (511558248967845956379/100000000000000000000)
  directionLo := (64248558513136668341/12500000000000000000)
  directionHi := (513988468105093346729/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree107.table
  base := (21945242003033033746744597492002227582207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-45353043112486689348939477525036112400000000000000)
      constant := (1352123655209096666487847269050022420646340103297784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree107.table
  base := (87780961314285965388814235416183259411033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-90798411483332201048341851726378474800000000000000)
      constant := (2709674345109455466333830323042100382859192911768548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64248558513136668341/12500000000000000000)
  centralHi := (513988468105093346729/100000000000000000000)
  directionLo := (258203625363293675741/50000000000000000000)
  directionHi := (516407250726587351483/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree108.table
  base := (18083735216009177530026602667451893556817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-45759999045686268539334997042915362400000000000000)
      constant := (1376800070473775995788272425350407406602979264865130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree108.table
  base := (11302333754148302020950934046559291337849/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-91613186202613217581940955217055724800000000000000)
      constant := (2759127049279136932089729961424335208253232713573152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258203625363293675741/50000000000000000000)
  centralHi := (516407250726587351483/100000000000000000000)
  directionLo := (518814756787973740781/100000000000000000000)
  directionHi := (259407378393986870391/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree109.table
  base := (46544885059589239652870996551455551918393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-46166954978885847729730516560794612400000000000000)
      constant := (1401699376908470704858700517507571618216508793124708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree109.table
  base := (46544882330240233682092061363392793792263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-92427960921894234115540058707732974800000000000000)
      constant := (2809026446004328545541872374141277478233542263468856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518814756787973740781/100000000000000000000)
  centralHi := (259407378393986870391/50000000000000000000)
  directionLo := (260605571275316482257/50000000000000000000)
  directionHi := (104242228510126592903/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree110.table
  base := (95794249537252253333807566495575529817221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-46573910912085426920126036078673862400000000000000)
      constant := (1426821574365040911533102770735349207039691843320138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree110.table
  base := (23948561152475805851142084956780214257091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-93242735641175250649139162198410224800000000000000)
      constant := (2859372534991758353653778436870363183884837041383984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260605571275316482257/50000000000000000000)
  centralHi := (104242228510126592903/20000000000000000000)
  directionLo := (523596560700037571301/100000000000000000000)
  directionHi := (261798280350018785651/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree111.table
  base := (3941284552179091352355080625247583601191/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-46980866845285006110521555596553112400000000000000)
      constant := (1452166662710976100984309247049255974082486312569950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree111.table
  base := (49266054678553878855004254414494066918609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-94057510360456267182738265689087474800000000000000)
      constant := (2910165315979128121638811368770084386668984369046408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523596560700037571301/100000000000000000000)
  centralHi := (261798280350018785651/50000000000000000000)
  directionLo := (525971160459278433411/100000000000000000000)
  directionHi := (131492790114819608353/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree112.table
  base := (25325840611737897944306867058569650405687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-47387822778484585300917075114432362400000000000000)
      constant := (1477734641827744394564237272340525657205150871311544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree112.table
  base := (25325839608279668164527917213150426531803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-94872285079737283716337369179764724800000000000000)
      constant := (2961404788731838555176058055261149120355189206858672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525971160459278433411/100000000000000000000)
  centralHi := (131492790114819608353/25000000000000000000)
  directionLo := (105667017539599727847/20000000000000000000)
  directionHi := (132083771924499659809/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree113.table
  base := (13013499380094886888515455028702540642213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-47794778711684164491312594632311612400000000000000)
      constant := (1503525511609316335052583274967723994751470233746512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree113.table
  base := (13013498927309809048599662759352410569217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-95687059799018300249936472670441974800000000000000)
      constant := (3013090953040061093907593356112287116624543268803616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105667017539599727847/20000000000000000000)
  centralHi := (132083771924499659809/25000000000000000000)
  directionLo := (265344242518480041139/50000000000000000000)
  directionHi := (530688485036960082279/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree114.table
  base := (106946011206691426649993672829718581580167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-48201734644883743681708114150190862400000000000000)
      constant := (1529539271960844713208347330517362123252440995109326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree114.table
  base := (6684125496125833043584073649994498999289/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-96501834518299316783535576161119224800000000000000)
      constant := (3065223808716119548867592873868561273650373997012544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265344242518480041139/50000000000000000000)
  centralHi := (530688485036960082279/100000000000000000000)
  directionLo := (533031491948454859041/100000000000000000000)
  directionHi := (266515745974227429521/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree115.table
  base := (109817410605527590806609118114869144921877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-48608690578083322872103633668070112400000000000000)
      constant := (1555775922797483920296858278941237395631593765081706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree115.table
  base := (109817407656152616271373409013974714921769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-97316609237580333317134679651796474800000000000000)
      constant := (3117803355592148756356148830978284445078148424464164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533031491948454859041/100000000000000000000)
  centralHi := (266515745974227429521/50000000000000000000)
  directionLo := (107072848970552303933/20000000000000000000)
  directionHi := (267682122426380759833/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree116.table
  base := (14090274116726553802194300986804390217173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-49015646511282902062499153185949362400000000000000)
      constant := (1582235464043334062540323596268218402936260070473552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree116.table
  base := (56361095136371779647620941861191894104047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-98131383956861349850733783142473724800000000000000)
      constant := (3170829593518000905311519185886083314460753845215864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107072848970552303933/20000000000000000000)
  centralHi := (267682122426380759833/50000000000000000000)
  directionLo := (537686877210834932037/100000000000000000000)
  directionHi := (268843438605417466019/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree117.table
  base := (57830178960040566528859009679012494428197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-49422602444482481252894672703828612400000000000000)
      constant := (1608917895630496638492012686876946329611222656045332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree117.table
  base := (115660355519308555765598363360563097908603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-98946158676142366384332886633150974800000000000000)
      constant := (3224302522359373308875765509324247182956827439535468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537686877210834932037/100000000000000000000)
  centralHi := (268843438605417466019/50000000000000000000)
  directionLo := (539999519613407964987/100000000000000000000)
  directionHi := (134999879903351991247/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree118.table
  base := (59315952660741299029786714939646427929673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-49829558377682060443290192221707862400000000000000)
      constant := (1635823217498229979046788699140225665670240933268388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree118.table
  base := (118631903155698307978935463529825156205417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-99760933395423382917931990123828224800000000000000)
      constant := (3278222141996134173230849773290270332577578516207652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539999519613407964987/100000000000000000000)
  centralHi := (134999879903351991247/25000000000000000000)
  directionLo := (542302299866673316273/100000000000000000000)
  directionHi := (271151149933336658137/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree119.table
  base := (30409208730189870916896732517882581844527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-50236514310881639633685711739587112400000000000000)
      constant := (1662951429592193899921760815821703900479817792533624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree119.table
  base := (121636832967098858289540171099363153462821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-100575708114704399451531093614505474800000000000000)
      constant := (3332588452320825403283809927932996804239955899033876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542302299866673316273/100000000000000000000)
  centralHi := (271151149933336658137/50000000000000000000)
  directionLo := (272297671537352278929/50000000000000000000)
  directionHi := (544595343074704557859/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree120.table
  base := (31168786630886805275002123289267137609877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-50643470244081218824081231257466362400000000000000)
      constant := (1690302531863774133813827015172277867311871191782824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree120.table
  base := (62337572380677535760773445058749000391003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-101390482833985415985130197105182724800000000000000)
      constant := (3387401453237323706979367267002836775745277083019736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272297671537352278929/50000000000000000000)
  centralHi := (544595343074704557859/100000000000000000000)
  directionLo := (136719692929691699943/25000000000000000000)
  directionHi := (546878771718766799773/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree121.table
  base := (31936709988989568868257949704184966069449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-51050426177280798014476750775345612400000000000000)
      constant := (1717876524269478108210910311603776717045021043612488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree121.table
  base := (127746838366577075705942328637427160090289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-102205257553266432518729300595859974800000000000000)
      constant := (3442661144659643246106640885999490484712450944809284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136719692929691699943/25000000000000000000)
  centralHi := (546878771718766799773/100000000000000000000)
  directionLo := (137288176433414810879/25000000000000000000)
  directionHi := (549152705733659243517/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree122.table
  base := (130851915062421503032556573863058459339469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-51457382110480377204872270293224862400000000000000)
      constant := (1745673406770394527630944061477025696604242541342682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree122.table
  base := (523407654515998885661051068658301874001/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-103020032272547449052328404086537224800000000000000)
      constant := (3498367526510864856612001763618834298570307445489000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137288176433414810879/25000000000000000000)
  centralHi := (549152705733659243517/100000000000000000000)
  directionLo := (551417262581224268539/100000000000000000000)
  directionHi := (27570863129061213427/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree123.table
  base := (8374398231484352814560226594604628708869/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-51864338043679956395267789811104112400000000000000)
      constant := (1773693179331710017165852430316118378447708381054112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree123.table
  base := (13399037041106829180961411811338219230233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-103834806991828465585927507577214474800000000000000)
      constant := (3554520598722178448105302502230582340774116493237480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551417262581224268539/100000000000000000000)
  centralHi := (27570863129061213427/5000000000000000000)
  directionLo := (553672557321150535953/100000000000000000000)
  directionHi := (276836278660575267977/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree124.table
  base := (68581104877705425586376831846082862075209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-52271293976879535585663309328983362400000000000000)
      constant := (1801935841922276797689775423819414815131132468432804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree124.table
  base := (137162208589726530704229651718495897379159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-104649581711109482119526611067891724800000000000000)
      constant := (3611120361232026610519663034600110850299336255159004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553672557321150535953/100000000000000000000)
  centralHi := (276836278660575267977/50000000000000000000)
  directionLo := (555918702679190869863/100000000000000000000)
  directionHi := (69489837834898858733/12500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree125.table
  base := (17545928638247834464213200923711116541267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-52678249910079114776058828846862612400000000000000)
      constant := (1830401394514226000948408729666927605992324774921008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree125.table
  base := (140367428054885590348064958119653219727379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-105464356430390498653125714558568974800000000000000)
      constant := (3668166813985338723677705708273695436315242948197324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555918702679190869863/100000000000000000000)
  centralHi := (69489837834898858733/12500000000000000000)
  directionLo := (3488473806955683493/625000000000000000)
  directionHi := (558155809112909358881/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree126.table
  base := (143606029655769269403725730709849667127443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-53085205843278693966454348364741862400000000000000)
      constant := (1859089837082621803015976600777238545675556238913254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree126.table
  base := (28721205741610953232755550356186765950261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-106279131149671515186724818049246224800000000000000)
      constant := (3725659956932845998836660974422478948566044801532580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3488473806955683493/625000000000000000)
  centralHi := (558155809112909358881/100000000000000000000)
  directionLo := (280191992437533090447/50000000000000000000)
  directionHi := (112076796975013236179/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree127.table
  base := (73439005657782264398345352894003125069657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-53492161776478273156849867882621112400000000000000)
      constant := (1888001169605152064467172392322884535242457575301092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree127.table
  base := (146878010461116911024011128040445523873199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-107093905868952531720323921539923474800000000000000)
      constant := (3783599790030468894428988543375909560041678270941244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280191992437533090447/50000000000000000000)
  centralHi := (112076796975013236179/20000000000000000000)
  directionLo := (562603336074743067527/100000000000000000000)
  directionHi := (70325417009342883441/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree128.table
  base := (18772921750693223394807472098027347745209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-53899117709677852347245387400500362400000000000000)
      constant := (1917135392061851621477218220745032275472658235811216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree128.table
  base := (18772921654404154032436921152917377161037/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-107908680588233548253923025030600724800000000000000)
      constant := (3841986313238769253956305147551623591903345853762976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell128.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562603336074743067527/100000000000000000000)
  centralHi := (70325417009342883441/12500000000000000000)
  directionLo := (282406983368153533677/50000000000000000000)
  directionHi := (112962793347261413471/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree129.table
  base := (76761058827142130389044795686168962478123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16746061631)
      previous := (0)
      next := (15019048575)
      square := (385971351112788914103391974255250000000000000000)
      linear := (-54306073642877431537640906918379612400000000000000)
      constant := (1946492504434854779664549887343971371360696944236588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 23607
  qDenominator := 44732
  table := BinomialMassData.Q23607_44732.Degree129.table
  base := (9595132309991487082543214422613418915479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (33527629287)
      previous := (0)
      next := (30002591125)
      square := (771942702225577828206783948510500000000000000000)
      linear := (-108723455307514564787522128521277974800000000000000)
      constant := (3900819526522460323742699682552832065153215227534784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23607_44732.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell128.Kernel129
