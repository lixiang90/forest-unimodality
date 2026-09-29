import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell188.Parameters
import ForestUnimodality.BinomialMassData.Q643_1188.Batch000_049
import ForestUnimodality.BinomialMassData.Q643_1188.Batch050_099
import ForestUnimodality.BinomialMassData.Q859_1584.Batch000_049
import ForestUnimodality.BinomialMassData.Q859_1584.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree000.table
  base := (662702396841997990262029817/20000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-3792964285623855444917751327600000000000000)
      constant := (196822611862073403107822855649000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree000.table
  base := (662702396841997990262029817/20000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-5057285714165140593223668436800000000000000)
      constant := (262430149149431204143763807532000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree001.table
  base := (2539002656848601224657294016256173557461/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-132645159858693934061546480765100000000000000)
      constant := (3321253286499534346420991260379283421164761440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree001.table
  base := (50718621009628049994944616246814338152587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-58979527696093839224389387334100000000000000)
      constant := (1474423062803268531474788507142836034406560544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6227595855657925119/12500000000000000000)
  directionHi := (49820766845263400953/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree002.table
  base := (128465210946658209994284870513150722013467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-162880284005543771110313675685000000000000000)
      constant := (2203912322167790903204122549808361279651983746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree002.table
  base := (128181964993341275970927958488437196510471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-72443483964701413109765758737000000000000000)
      constant := (977650003910597988723994795832842836726637288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6227595855657925119/12500000000000000000)
  centralHi := (49820766845263400953/100000000000000000000)
  directionLo := (35228602080199669263/50000000000000000000)
  directionHi := (70457204160399338527/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree003.table
  base := (20945385802721117017008201965060080547119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-21457267572488178684342318956100000000000000)
      constant := (175957360451389955490262813859110754139864232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree003.table
  base := (83531053344004429084066538026143499638279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-9545271137034331888349125571100000000000000)
      constant := (78034999868887442362678264454571276713516968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35228602080199669263/50000000000000000000)
  centralHi := (70457204160399338527/100000000000000000000)
  directionLo := (86292099448039220751/100000000000000000000)
  directionHi := (5393256215502451297/6250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree004.table
  base := (2244202810248851837358786358532519939059/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-223350532299243445207848065524800000000000000)
      constant := (1252446189548956082990122203468613869565706050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree004.table
  base := (55902666501327230803584867076788819278157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-99371396501916560880518501542800000000000000)
      constant := (555618026835800182635853909177600703814703096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86292099448039220751/100000000000000000000)
  centralHi := (5393256215502451297/6250000000000000000)
  directionLo := (6227595855657925119/6250000000000000000)
  directionHi := (19928306738105360381/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree005.table
  base := (38264816199401966605172200407122981634513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-253585656446093282256615260444700000000000000)
      constant := (1095394047411298586521118528884500879454319494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree005.table
  base := (38106565711693103281005064787495601947419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-112835352770524134765894872945700000000000000)
      constant := (486307066122258625935293048372909275681202632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6227595855657925119/6250000000000000000)
  centralHi := (19928306738105360381/20000000000000000000)
  directionLo := (22280524271435342187/20000000000000000000)
  directionHi := (13925327669647088867/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree006.table
  base := (26255276839700258218170892300215031387609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-31535642288104791033931383929400000000000000)
      constant := (116468837919809995973225535577833185932719238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree006.table
  base := (26132377093711645601853516018800872611839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-14033256559903523183474582705400000000000000)
      constant := (51755130183645725938228207662552791108576488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22280524271435342187/20000000000000000000)
  centralHi := (13925327669647088867/12500000000000000000)
  directionLo := (122035457365064935349/100000000000000000000)
  directionHi := (2440709147301298707/2000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree007.table
  base := (17808807854543007457083891581996120911679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-314055904739792956354149650284500000000000000)
      constant := (1074554191504501821443743078410816287181507802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree007.table
  base := (17712765982030018730380033465536503836609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-139763265307739282536647615751500000000000000)
      constant := (477923781932823868515309035836559824347348952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122035457365064935349/100000000000000000000)
  centralHi := (2440709147301298707/2000000000000000000)
  directionLo := (131813359199098929959/100000000000000000000)
  directionHi := (3295333979977473249/2500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree008.table
  base := (580941439381211026555999405572122829519/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-344291028886642793402916845204400000000000000)
      constant := (1153443060731698631158548875273714118796514440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree008.table
  base := (11542883834296249758916305253030724610717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-153227221576346856422023987154400000000000000)
      constant := (513388936552410768263198821951003005025190776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131813359199098929959/100000000000000000000)
  centralHi := (3295333979977473249/2500000000000000000)
  directionLo := (35228602080199669263/25000000000000000000)
  directionHi := (140914408320798677053/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree009.table
  base := (3457736015425705138871219865300925817177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-13871339001240467794506816300900000000000000)
      constant := (47131074528196040140395664446664999870806276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree009.table
  base := (1370927424052414060182116562448021392327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-18521241982772714478600039839700000000000000)
      constant := (62968518314218063958709151500684789713614920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35228602080199669263/25000000000000000000)
  centralHi := (140914408320798677053/100000000000000000000)
  directionLo := (18682787566973775357/12500000000000000000)
  directionHi := (149462300535790202857/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree010.table
  base := (3232604279861884865817871689419228313277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-404761277180342467500451235044200000000000000)
      constant := (1424366200157916327752428208528155583688336526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree010.table
  base := (1591653794313109564216301570426680469803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-180155134113562004192776729960200000000000000)
      constant := (634594455064203900578172745821565256777511568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18682787566973775357/12500000000000000000)
  centralHi := (149462300535790202857/100000000000000000000)
  directionLo := (4923346812726059909/3125000000000000000)
  directionHi := (157547098007233917089/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree011.table
  base := (69753326243686217395108595663216680249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-434996401327192304549218429964100000000000000)
      constant := (1604254162681946098053351984709449176471333848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree011.table
  base := (119351982087105315110528071609621265963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-193619090382169578078153101363100000000000000)
      constant := (714953823851405889675499350535407385767568528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4923346812726059909/3125000000000000000)
  centralHi := (157547098007233917089/100000000000000000000)
  directionLo := (165236790393516982697/100000000000000000000)
  directionHi := (82618395196758491349/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree012.table
  base := (-1066754190368724133887132893243827566099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-51692391719338015733109513876000000000000000)
      constant := (201020492017560015013269489344278998554423164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree012.table
  base := (-1083339050322151631272009912889465435537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-23009227405641905773725496974000000000000000)
      constant := (89606471133358851320645943449033086750109392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165236790393516982697/100000000000000000000)
  centralHi := (82618395196758491349/50000000000000000000)
  directionLo := (86292099448039220751/50000000000000000000)
  directionHi := (172584198896078441503/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree013.table
  base := (-4130846840233373438042065840989379745081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-495466649620891978646752819803900000000000000)
      constant := (2037138035908467146884026832520674827648390922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree013.table
  base := (-4158248583701395993247544425942551024859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-220547002919384725848905844168900000000000000)
      constant := (908213781788403077704667460004172121294805048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86292099448039220751/50000000000000000000)
  centralHi := (172584198896078441503/100000000000000000000)
  directionLo := (35926265888706697081/20000000000000000000)
  directionHi := (89815664721766742703/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree014.table
  base := (-181249528457663658760876987378337631979/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-525701773767741815695520014723800000000000000)
      constant := (2286719955191300806476467951214889073866265536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree014.table
  base := (-727833337041117096517518539616030017379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-234010959187992299734282215571800000000000000)
      constant := (1019602741757552573401394762081998004288979904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35926265888706697081/20000000000000000000)
  centralHi := (89815664721766742703/50000000000000000000)
  directionLo := (186412240281322076611/100000000000000000000)
  directionHi := (46603060070330519153/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree015.table
  base := (-7202783980102536948573593555740357529601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-61770766434954628082698578849300000000000000)
      constant := (284104228118191136546666657489733182882251018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree015.table
  base := (-7221569285281864302229674396010256945569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-27497212828511097068850954108300000000000000)
      constant := (126687308073778771766772832567000501499109352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186412240281322076611/100000000000000000000)
  centralHi := (46603060070330519153/25000000000000000000)
  directionLo := (192955000286987779147/100000000000000000000)
  directionHi := (48238750071746944787/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree016.table
  base := (-8384316435610670611602516669562499655963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-586172022061441489793054404563600000000000000)
      constant := (2847069458582932848004863369187956630517665406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree016.table
  base := (-2099966949149225602384449443005638846961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-260938871725207447505034958377600000000000000)
      constant := (1269642745720422427771467152891423225195447968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192955000286987779147/100000000000000000000)
  centralHi := (48238750071746944787/25000000000000000000)
  directionLo := (199283067381053603809/100000000000000000000)
  directionHi := (19928306738105360381/10000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree017.table
  base := (-937806287434298022500106338198423768889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-616407146208291326841821599483500000000000000)
      constant := (3156577209931472602240087102688499295945582180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree017.table
  base := (-4695461463911218640928017051748193315793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-274402827993815021390411329780500000000000000)
      constant := (1407735865874668122266351817833243381090054992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199283067381053603809/100000000000000000000)
  centralHi := (19928306738105360381/10000000000000000000)
  directionLo := (41083256810458271063/20000000000000000000)
  directionHi := (51354071013072838829/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree018.table
  base := (-10209265318601853923089983199612187457463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-23949713716857080144095881274200000000000000)
      constant := (129076165761320510767682775456380360650266978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree018.table
  base := (-10219883889088116278977026226147705014381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-31985198251380288363976411242600000000000000)
      constant := (172698429950771322556111947755053517628610248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41083256810458271063/20000000000000000000)
  centralHi := (51354071013072838829/25000000000000000000)
  directionLo := (211371612481198015579/100000000000000000000)
  directionHi := (10568580624059900779/5000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree019.table
  base := (-2724291588038182806986583387987825414839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-676877394501991000939355989323300000000000000)
      constant := (3832198642897046294411835026034867523987248472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree019.table
  base := (-2726479755966970649701158306083674412811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-301330740531030169161164072586300000000000000)
      constant := (1709156124814961502872775581224832900141932768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211371612481198015579/100000000000000000000)
  centralHi := (10568580624059900779/5000000000000000000)
  directionLo := (3393182624503200843/1562500000000000000)
  directionHi := (217163687968204853953/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree020.table
  base := (-11456553929846663778276050249636538793697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-707112518648840837988123184243200000000000000)
      constant := (4197766542735748947111721570295329190826687514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree020.table
  base := (-5731877707786646342731784643764245211283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-314794696799637743046540443989200000000000000)
      constant := (1872241656998169347535935009378746920267949552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3393182624503200843/1562500000000000000)
  centralHi := (217163687968204853953/100000000000000000000)
  directionLo := (222805242714353421871/100000000000000000000)
  directionHi := (13925327669647088867/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree021.table
  base := (-11898858590403868956342849797877417109681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-81927515866187852781876708795900000000000000)
      constant := (509064094676862989161149898310344942710548458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree021.table
  base := (-11904772861081826127393194113883027377073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-36473183674249479659101868376900000000000000)
      constant := (227051261212713640276454450925420267317358184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222805242714353421871/100000000000000000000)
  centralHi := (13925327669647088867/6250000000000000000)
  directionLo := (228307435249165802341/100000000000000000000)
  directionHi := (114153717624582901171/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree022.table
  base := (-3058238007866632168110223421074917364291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-767582766942540512085657574083000000000000000)
      constant := (4983487286678314846950419807589651901246003768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree022.table
  base := (-12237800349248459494419464382523764617519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-341722609336852890817293186795000000000000000)
      constant := (2222752273531163474739521308866133105806324568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228307435249165802341/100000000000000000000)
  centralHi := (114153717624582901171/50000000000000000000)
  directionLo := (233680109977512062183/100000000000000000000)
  directionHi := (29210013747189007773/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree023.table
  base := (-1246573980806635921553646374312708077661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-797817891089390349134424769002900000000000000)
      constant := (5403387095203794114769492510627690378504728820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree023.table
  base := (-12469707322289157562991588882975051544033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-355186565605460464702669558197900000000000000)
      constant := (2410065459464276087363698800739069457594132776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233680109977512062183/100000000000000000000)
  centralHi := (29210013747189007773/12500000000000000000)
  directionLo := (119466002076063704447/50000000000000000000)
  directionHi := (47786400830425481779/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree024.table
  base := (-39383149694542863965780081624031768629/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-92005890581804465131465773769200000000000000)
      constant := (649021099698675677583252908118712124256999040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree024.table
  base := (-6302924595805799765948661227472000136847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-40961169097118670954227325511200000000000000)
      constant := (289484748371249629225740379716684351783234352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119466002076063704447/50000000000000000000)
  centralHi := (47786400830425481779/20000000000000000000)
  directionLo := (122035457365064935349/50000000000000000000)
  directionHi := (244070914730129870699/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree025.table
  base := (-2529552598905666203064549880222299135179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-858288139383090023231959158842700000000000000)
      constant := (6296828226189321118310163887511536332349995990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree025.table
  base := (-12650406785053641215431253053691201826217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-382114478142675612473422301003700000000000000)
      constant := (2808614300221246965499123336054304738382725224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122035457365064935349/50000000000000000000)
  centralHi := (244070914730129870699/100000000000000000000)
  directionLo := (249103834226317004761/100000000000000000000)
  directionHi := (124551917113158502381/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree026.table
  base := (-6302246937347294994540512530316011753701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-888523263529939860280726353762600000000000000)
      constant := (6770249336296631414085433033109233606988286724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree026.table
  base := (-157583088494759048109096309535621058487/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-395578434411283186358798672406600000000000000)
      constant := (3019796867092467329642041094483369947608373120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249103834226317004761/100000000000000000000)
  centralHi := (124551917113158502381/50000000000000000000)
  directionLo := (127018531163077263943/50000000000000000000)
  directionHi := (254037062326154527887/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree027.table
  base := (-12475373454135006316890231715330510064879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-34028088432473692493684946247500000000000000)
      constant := (268941183824342934935511913051881177021461874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree027.table
  base := (-1247712463667437117823173177304624345701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-45449154519987862249352782645500000000000000)
      constant := (359876914115629717132861816274063000182048080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127018531163077263943/50000000000000000000)
  centralHi := (254037062326154527887/100000000000000000000)
  directionLo := (129438149172058831127/50000000000000000000)
  directionHi := (51775259668823532451/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree028.table
  base := (-12262415529002434862917203152284501646667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-948993511823639534378260743602400000000000000)
      constant := (7770283809808505119518822065109061162590754654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree028.table
  base := (-12263837865863151288033538253258550366777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-422506346948498334129551415212400000000000000)
      constant := (3465886135402727705856874116687423052985613544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129438149172058831127/50000000000000000000)
  centralHi := (51775259668823532451/20000000000000000000)
  directionLo := (263626718398197859919/100000000000000000000)
  directionHi := (3295333979977473249/1250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree029.table
  base := (-2393439357419184207380681839750210420227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-979228635970489371427027938522300000000000000)
      constant := (8296839589031447952584000578144493126401996870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree029.table
  base := (-2992087648925655463587893451367604027703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-435970303217105908014927786615300000000000000)
      constant := (3700767445208704069509309296382997498962132064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263626718398197859919/100000000000000000000)
  centralHi := (3295333979977473249/1250000000000000000)
  directionLo := (268293040279565975433/100000000000000000000)
  directionHi := (134146520139782987717/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree030.table
  base := (-2318190391824995292835015719366200117167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-112162640013037689830643903715800000000000000)
      constant := (982339944257218732778597237215697156956042030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree030.table
  base := (-11591886844591644744294254960582038825943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-49937139942857053544478239779800000000000000)
      constant := (438169714628383273084923676946781525249853144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268293040279565975433/100000000000000000000)
  centralHi := (134146520139782987717/50000000000000000000)
  directionLo := (272879578333562564647/100000000000000000000)
  directionHi := (34109947291695320581/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree031.table
  base := (-2783662032896369794044853938449331780509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1039698884264189045524562328362100000000000000)
      constant := (9402928027525846154920595471215560967616786632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree031.table
  base := (-278385120066861432498294308382492328063/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-462898215754321055785680529421100000000000000)
      constant := (4194159264763615746847609186385649412422677440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272879578333562564647/100000000000000000000)
  centralHi := (34109947291695320581/12500000000000000000)
  directionLo := (277390290169921060983/100000000000000000000)
  directionHi := (34673786271240132623/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree032.table
  base := (-2649760710586738181027562406846361947529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1069934008411038882573329523282000000000000000)
      constant := (9982433027271729213609614958143192188342119592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree032.table
  base := (-1059965464095570649384427472887482752661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-476362172022928629671056900824000000000000000)
      constant := (4452657597314281813138646277335780229390323920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277390290169921060983/100000000000000000000)
  centralHi := (34673786271240132623/12500000000000000000)
  directionLo := (56365763328319470821/20000000000000000000)
  directionHi := (140914408320798677053/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree033.table
  base := (-4992364764579025783586340896813334004939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-122241014728654302180232968689100000000000000)
      constant := (1175507219999778316761966908516419777606397404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree033.table
  base := (-998522371328635079103496366279476839227/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-54425125365726244839603696914100000000000000)
      constant := (524335360294355336077653504991807168433322160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56365763328319470821/20000000000000000000)
  centralHi := (140914408320798677053/50000000000000000000)
  directionLo := (286198516241180395559/100000000000000000000)
  directionHi := (7154962906029509889/2500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree034.table
  base := (-4646086550551430756090433164804182051589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1130404256704738556670863913121800000000000000)
      constant := (11194316429492782498495171723640991056513231236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree034.table
  base := (-9292571916928673101665415146197381826107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-503290084560143777441809643629800000000000000)
      constant := (4993237922620678828944683275363967562343509304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286198516241180395559/100000000000000000000)
  centralHi := (7154962906029509889/2500000000000000000)
  directionLo := (58100498967806910077/20000000000000000000)
  directionHi := (145251247419517275193/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree035.table
  base := (-8521737788630424194143445913497763203947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1160639380851588393719631108041700000000000000)
      constant := (11826681534228120426779754987850385373735098014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree035.table
  base := (-2130514840798531344439150277205419502361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-516754040828751351327186015032700000000000000)
      constant := (5275314070355296196362045980733709704148683168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58100498967806910077/20000000000000000000)
  centralHi := (145251247419517275193/50000000000000000000)
  directionLo := (147371815755891221657/50000000000000000000)
  directionHi := (58948726302356488663/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree036.table
  base := (-479606809572036135260656084928299383013/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-44106463148090304843274011220800000000000000)
      constant := (462098359910285021075138835457041442663844448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree036.table
  base := (-7673968035250177665049707721275590999557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-58913110788595436134729154048400000000000000)
      constant := (618360519541892488940547387334599731928350856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147371815755891221657/50000000000000000000)
  centralHi := (58948726302356488663/20000000000000000000)
  directionLo := (298924601071580405713/100000000000000000000)
  directionHi := (149462300535790202857/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree037.table
  base := (-3374155084493043786280438982003168811811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1221109629145288067817165497881500000000000000)
      constant := (13144235393856615661799659358759528857192350364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree037.table
  base := (-6748518742248724332194528883755350957779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-543681953365966499097938757838500000000000000)
      constant := (5863028165258252738193589060276432483372951288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298924601071580405713/100000000000000000000)
  centralHi := (149462300535790202857/50000000000000000000)
  directionLo := (303047893797092056887/100000000000000000000)
  directionHi := (37880986724636507111/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree038.table
  base := (-1149143320777334675842104248431562528323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1251344753292137904865932692801400000000000000)
      constant := (13829417753724414452337676410423923000853778630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree038.table
  base := (-2872942196355765553455912141252512397781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-557145909634574072983315129241400000000000000)
      constant := (6168663306007014063440840128485266683257234064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303047893797092056887/100000000000000000000)
  centralHi := (37880986724636507111/12500000000000000000)
  directionLo := (153557916389797113007/50000000000000000000)
  directionHi := (61423166555918845203/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree039.table
  base := (-4666065500991844704402520552766585023037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-142397764159887526879411098635700000000000000)
      constant := (1614688955119516952152411051226032445488948066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree039.table
  base := (-1166550096752011698236148719389846797129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-63401096211464627429854611182700000000000000)
      constant := (720238792554386993903733286643863590346695328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153557916389797113007/50000000000000000000)
  centralHi := (61423166555918845203/20000000000000000000)
  directionLo := (155565294613671609427/50000000000000000000)
  directionHi := (62226117845468643771/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree040.table
  base := (-1754732195252991255879575978044131050611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1311815001585837578963467082641200000000000000)
      constant := (15252582196340912151007154447136256452420601564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree040.table
  base := (-3509572754611176756147535316288627598883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-584073822171789220754067872047200000000000000)
      constant := (6803484890427576513824055150758494662475161976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155565294613671609427/50000000000000000000)
  centralHi := (62226117845468643771/20000000000000000000)
  directionLo := (4923346812726059909/1562500000000000000)
  directionHi := (315094196014467834177/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree041.table
  base := (-227599752306347446764702622674131313277/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1342050125732687416012234277561100000000000000)
      constant := (15990561203308518887850853665126485319976634740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree041.table
  base := (-2276084525742877959577630748972970139081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-597537778440396794639444243450100000000000000)
      constant := (7132669986481872660279536651225236293848630632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4923346812726059909/1562500000000000000)
  centralHi := (315094196014467834177/100000000000000000000)
  directionLo := (12760342388575878591/4000000000000000000)
  directionHi := (39876069964299620597/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree042.table
  base := (-241432727501381936162587956931131308459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-152476138875504139229000163609000000000000000)
      constant := (1860681839809842499918765731075044896033304248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree042.table
  base := (-241450180156549154445100979159443268187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-67889081634333818724980068317000000000000000)
      constant := (829967106409802390120307066121885383726383584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12760342388575878591/4000000000000000000)
  centralHi := (39876069964299620597/12500000000000000000)
  directionLo := (322875471319987500553/100000000000000000000)
  directionHi := (161437735659993750277/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree043.table
  base := (42128372770296284346439061019614524989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1402520374026387090109768667400900000000000000)
      constant := (17519307431780268002238081374426788277517735820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree043.table
  base := (421227743668636753552048389034067096963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-624465690977611942410196986255900000000000000)
      constant := (7814586441109746463117882716442575455267152264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322875471319987500553/100000000000000000000)
  centralHi := (161437735659993750277/50000000000000000000)
  directionLo := (326696615821398076419/100000000000000000000)
  directionHi := (16334830791069903821/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree044.table
  base := (1885005865570868449624633112559102803269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1432755498173236927158535862320800000000000000)
      constant := (18310073173851786672309073204206222890758828222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree044.table
  base := (471240248481134069657090195514585732101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-637929647246219516295573357658800000000000000)
      constant := (8167317152530156128262253162790761868393663712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326696615821398076419/100000000000000000000)
  centralHi := (16334830791069903821/5000000000000000000)
  directionLo := (66094716157406793079/20000000000000000000)
  directionHi := (82618395196758491349/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree045.table
  base := (1712701875773253261925099742990005622397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-54184837863706917192863076194100000000000000)
      constant := (708090121306064208323899444563859626679407636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree045.table
  base := (1712683902570022145887281302443087502093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-72377067057203010020105525451300000000000000)
      constant := (947543985486404457363883430143835475603315312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66094716157406793079/20000000000000000000)
  centralHi := (82618395196758491349/25000000000000000000)
  directionLo := (334207864071530132807/100000000000000000000)
  directionHi := (41775983008941266601/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree046.table
  base := (5042452506806104628056499745331235445579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1493225746466936601256070252160600000000000000)
      constant := (19944387337009533197184716117299272354076196002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree046.table
  base := (5042423724573786383297372196949133159813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-664857559783434664066326100464600000000000000)
      constant := (8896322417353057910363682130277315921163147064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334207864071530132807/100000000000000000000)
  centralHi := (41775983008941266601/12500000000000000000)
  directionLo := (4223761009461540507/1250000000000000000)
  directionHi := (337900880756923240561/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree047.table
  base := (6736132637730823420637112909659529897841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1523460870613786438304837447080500000000000000)
      constant := (20787935046450526444266682766738882040501573958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree047.table
  base := (6736109602731471873217818343702564850707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-678321516052042237951702471867500000000000000)
      constant := (9272596659958814206561556832921877507255839496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4223761009461540507/1250000000000000000)
  centralHi := (337900880756923240561/100000000000000000000)
  directionLo := (341553969418237848793/100000000000000000000)
  directionHi := (170776984709118924397/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree048.table
  base := (8506428870044688615997177285878565991867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-172632888306737363928178293555600000000000000)
      constant := (2405452906513097254488757173301035604597506994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree048.table
  base := (850641044301607358192740178896897890779/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-76865052480072201315230982585600000000000000)
      constant := (1072968721144351710570258399614463431294969680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341553969418237848793/100000000000000000000)
  centralHi := (170776984709118924397/50000000000000000000)
  directionLo := (69033679558431376601/20000000000000000000)
  directionHi := (172584198896078441503/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree049.table
  base := (10353329235362817759613986555936896084679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1583931118907486112402371836920300000000000000)
      constant := (22527810481562622990775476332281678439406081802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree049.table
  base := (10353314500913874913215347680311340184991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-705249428589257385722455214673300000000000000)
      constant := (10048687824659217704178198017954024857838615848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69033679558431376601/20000000000000000000)
  centralHi := (172584198896078441503/50000000000000000000)
  directionLo := (69749073583368761333/20000000000000000000)
  directionHi := (174372683958421903333/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree050.table
  base := (12276824355501695143336901099716230656273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1614166243054335949451139031840200000000000000)
      constant := (23424137864877462320469348126228498907265306374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree050.table
  base := (3069203144646378802070351530927700217471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-718713384857864959607831586076200000000000000)
      constant := (10448504597476772170923245915948873088600533152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69749073583368761333/20000000000000000000)
  centralHi := (174372683958421903333/50000000000000000000)
  directionLo := (44035752600249586579/12500000000000000000)
  directionHi := (352286020801996692633/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree051.table
  base := (14276906881735314597221424408101112486461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-182711263022353976277767358528900000000000000)
      constant := (2704228687855947288058540011837398682450873502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree051.table
  base := (14276897472473960257555924629388510213917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-81353037902941392610356439719900000000000000)
      constant := (1206240973044986028391295200840841325089422264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44035752600249586579/12500000000000000000)
  centralHi := (352286020801996692633/100000000000000000000)
  directionLo := (35579144068056913189/10000000000000000000)
  directionHi := (355791440680569131891/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree052.table
  base := (16353571055451092242810313853268877408803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1674636491348035623548673421680000000000000000)
      constant := (25269571366684184186705315015940926255882382514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree052.table
  base := (817678177036826992745913442398343138327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-745641297395080107378584328882000000000000000)
      constant := (11271680264228469404744202811167757797799897120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35579144068056913189/10000000000000000000)
  centralHi := (355791440680569131891/100000000000000000000)
  directionLo := (35926265888706697081/10000000000000000000)
  directionHi := (359262658887066970811/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree053.table
  base := (9253406181961189299128037399013472392703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1704871615494885460597440616599900000000000000)
      constant := (26218677320444328098614842735450218640468341428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree053.table
  base := (9253403182254301558813686541488107882203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-759105253663687681263960700284900000000000000)
      constant := (11695039086449890387098705610464995090968685968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35926265888706697081/10000000000000000000)
  centralHi := (359262658887066970811/100000000000000000000)
  directionLo := (181350328700870526731/50000000000000000000)
  directionHi := (362700657401741053463/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree054.table
  base := (829465090824192250729869988373100633541/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-64263212579323529542452141167400000000000000)
      constant := (1006865777602402176443312225561090544408083850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree054.table
  base := (10368311241322370518900347030643082798657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-85841023325810583905481896854200000000000000)
      constant := (1347360577710899191908553159667601143153072688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181350328700870526731/50000000000000000000)
  centralHi := (362700657401741053463/100000000000000000000)
  directionLo := (366106372095194806047/100000000000000000000)
  directionHi := (11440824127974837689/3125000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree055.table
  base := (1152150650191104612367764366141159761761/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1765341863788585134694975006439700000000000000)
      constant := (28169667346693631955928038031861000905182458360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree055.table
  base := (23043009183998790187451356852067018051391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-786033166200902829034713443090700000000000000)
      constant := (12565298583748026572064330846291049329670315048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366106372095194806047/100000000000000000000)
  centralHi := (11440824127974837689/3125000000000000000)
  directionLo := (184740347851894099361/50000000000000000000)
  directionHi := (369480695703788198723/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree056.table
  base := (5085193478240006038693431975953054628361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1795576987935434971743742201359600000000000000)
      constant := (29171551339890110153175833764390075450648268590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree056.table
  base := (25425964344761308005648780646274640832647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-799497122469510402920089814493600000000000000)
      constant := (13012199224361178215186449658306045639855107816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184740347851894099361/50000000000000000000)
  centralHi := (369480695703788198723/100000000000000000000)
  directionLo := (372824480562644153223/100000000000000000000)
  directionHi := (46603060070330519153/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree057.table
  base := (871421522810757843822637573699684099143/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-202868012453587200976945488475500000000000000)
      constant := (3354558660838319696002080893857513286069530432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree057.table
  base := (3485685787635084375875153011748451054421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-90329008748679775200607353988500000000000000)
      constant := (1496327456597512590316829171190128810880811456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372824480562644153223/100000000000000000000)
  centralHi := (46603060070330519153/12500000000000000000)
  directionLo := (188069270559982449347/50000000000000000000)
  directionHi := (75227708223992979739/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree058.table
  base := (304215756852016396207458562905444520167/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1856047236229134645841276591199400000000000000)
      constant := (31228097148249559029233801453331401921443834600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree058.table
  base := (3042157374931413211870425729138107368771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-826425035006725550690842557299400000000000000)
      constant := (13929542229504966278388419517151926793245996880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188069270559982449347/50000000000000000000)
  centralHi := (75227708223992979739/20000000000000000000)
  directionLo := (47427957031709159861/12500000000000000000)
  directionHi := (379423656253673278889/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree059.table
  base := (33034227210425359296172917942140090126553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1886282360375984482890043786119300000000000000)
      constant := (32282758925219637280983519103544105265449657014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree059.table
  base := (8258556416978826434340487966859997998473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-839888991275333124576218928702300000000000000)
      constant := (14399984577461654560752314410199752887932462176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47427957031709159861/12500000000000000000)
  centralHi := (379423656253673278889/100000000000000000000)
  directionLo := (95670142852262076181/25000000000000000000)
  directionHi := (15307222856361932189/4000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree060.table
  base := (35723442484979762530499056092298745358627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-212946387169203813326534553448800000000000000)
      constant := (3706112585032639722743694271959476364229073314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree060.table
  base := (2232715078516554652821664336427021506313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-94816994171548966495732811122800000000000000)
      constant := (1653141571948984848541874614215453216527998336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95670142852262076181/25000000000000000000)
  centralHi := (15307222856361932189/4000000000000000000)
  directionLo := (77182000114795111659/20000000000000000000)
  directionHi := (48238750071746944787/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree061.table
  base := (1202788152039150327242758435869295053331/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1946752608669684156987578175959100000000000000)
      constant := (34444860158149669821255319144883558630090322496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree061.table
  base := (38489219886769113029861553890912549024139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-866816903812548272346971671508100000000000000)
      constant := (15364410935269105433449552536542215274444062792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77182000114795111659/20000000000000000000)
  centralHi := (48238750071746944787/12500000000000000000)
  directionLo := (97278157026659867439/25000000000000000000)
  directionHi := (389112628106639469757/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree062.table
  base := (10332890461587919791814833521561075160637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-1976987732816533994036345370879000000000000000)
      constant := (35552299595689903120115988181963636093705184824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree062.table
  base := (41331561067348287873684275431463204320419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-880280860081155846232348042911000000000000000)
      constant := (15858394937138835609242519012692732220395946632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97278157026659867439/25000000000000000000)
  centralHi := (389112628106639469757/100000000000000000000)
  directionLo := (9807227760722764819/2500000000000000000)
  directionHi := (392289110428910592761/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree063.table
  base := (11062616258022585897694870950805643138641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-74341587294940141892041206140700000000000000)
      constant := (1358419687835571330811302814761001708097411016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree063.table
  base := (44250464412061178616494042874449939687021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-99304979594418157790858268257100000000000000)
      constant := (1817802905599896127280981138037304977232120632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9807227760722764819/2500000000000000000)
  centralHi := (392289110428910592761/100000000000000000000)
  directionLo := (197720038798648394939/50000000000000000000)
  directionHi := (395440077597296789879/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree064.table
  base := (9449186022294794829865367554123193921859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2037457981110233668133879760718800000000000000)
      constant := (37819956080773503179610318421893138920593873210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree064.table
  base := (47245929618100878108683505261977854828211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-907208772618370994003100785716800000000000000)
      constant := (16869904572891386408146085027843378149215488008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197720038798648394939/50000000000000000000)
  centralHi := (395440077597296789879/100000000000000000000)
  directionLo := (199283067381053603809/50000000000000000000)
  directionHi := (398566134762107207619/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree065.table
  base := (50317956840273630868727009251215891259683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2067693105257083505182646955638700000000000000)
      constant := (38980173119412191123925606637510562964022795954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree065.table
  base := (50317956447779852302521901057357129225719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-920672728886978567888477157119700000000000000)
      constant := (17387430202921562654402058500982107242120925032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199283067381053603809/50000000000000000000)
  centralHi := (398566134762107207619/100000000000000000000)
  directionLo := (8033357270488006881/2000000000000000000)
  directionHi := (401667863524400344051/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree066.table
  base := (6683318128323656037910409132872787794667/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-233103136600437038025712683395400000000000000)
      constant := (4461998076044310723914772951881084462800772752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree066.table
  base := (5346654471442202780052005259009331227457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-103792965017287349085983725391400000000000000)
      constant := (1990311448795440759235494200368516403321459440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8033357270488006881/2000000000000000000)
  centralHi := (401667863524400344051/100000000000000000000)
  directionLo := (404745823199333827673/100000000000000000000)
  directionHi := (202372911599666913837/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree067.table
  base := (56691694519537486283691127653873844207273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2128163353550783179280181345478500000000000000)
      constant := (41353384773313452343897062614259091213396244374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree067.table
  base := (56691694271314431156191871108491560802407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-947600641424193715659229899925500000000000000)
      constant := (18446023080557828869571700094224918470399557096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404745823199333827673/100000000000000000000)
  centralHi := (202372911599666913837/50000000000000000000)
  directionLo := (203900275996843916873/50000000000000000000)
  directionHi := (407800551993687833747/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree068.table
  base := (59993405200387950827127876065071080449049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2158398477697633016328948540398400000000000000)
      constant := (42566379384251960551221414365673009988241847862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree068.table
  base := (14998351250763684247966172903714025533047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-961064597692801289544606271328400000000000000)
      constant := (18987090326295560988466764617603344295998236064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203900275996843916873/50000000000000000000)
  centralHi := (407800551993687833747/100000000000000000000)
  directionLo := (41083256810458271063/10000000000000000000)
  directionHi := (410832568104582710631/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree069.table
  base := (63371676975617748713865073231143963524799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-243181511316053650375301748368700000000000000)
      constant := (4866329612857155663972000779912461043001191818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree069.table
  base := (63371676818775037897165728433570472156191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-108280950440156540381109182525700000000000000)
      constant := (2170667197302717416198167128572903438947703272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41083256810458271063/10000000000000000000)
  centralHi := (410832568104582710631/100000000000000000000)
  directionLo := (206921185372871310601/50000000000000000000)
  directionHi := (413842370745742621203/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree070.table
  base := (2673060390858763605395188825916433240371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2218868725991332690426482930238200000000000000)
      constant := (45045146166517846184519729724866443907726752450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree070.table
  base := (33413254823417439029037969031971036981059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-987992510230016437315359014134200000000000000)
      constant := (20092766428333862972479590970810341603201977104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206921185372871310601/50000000000000000000)
  centralHi := (413842370745742621203/100000000000000000000)
  directionLo := (416830441107060683711/100000000000000000000)
  directionHi := (6512975642297823183/1562500000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree071.table
  base := (549671121325660634895922901840576481133/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2249103850138182527475250125158100000000000000)
      constant := (46310918335727963774635390732458015697364614912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree071.table
  base := (70357903430664868399377254350229845956593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1001456466498624011200735385537100000000000000)
      constant := (20657375283720553063226870683007853966978594904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416830441107060683711/100000000000000000000)
  centralHi := (6512975642297823183/1562500000000000000)
  directionLo := (419797243252688454277/100000000000000000000)
  directionHi := (209898621626344227139/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree072.table
  base := (36982929102082565615116589736525457263137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-84419962010556754241630271114000000000000000)
      constant := (1762751223059459906994709370120592243228606756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree072.table
  base := (36982929062755664046954503709353235420997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-112768935863025731676234639660000000000000000)
      constant := (2358870149062835864565482448765415524906859248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419797243252688454277/100000000000000000000)
  centralHi := (209898621626344227139/50000000000000000000)
  directionLo := (211371612481198015579/50000000000000000000)
  directionHi := (422743224962396031159/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree073.table
  base := (9706296719793893721609552616844148281529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2309574098431882201572784514997900000000000000)
      constant := (48895240226563863656432720005186534101113296816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree073.table
  base := (19412593423971632339829113856281256684737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1028384379035839158971488128342900000000000000)
      constant := (21810134601615815602434380438587206815595221344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211371612481198015579/50000000000000000000)
  centralHi := (422743224962396031159/100000000000000000000)
  directionLo := (53208602315065247441/12500000000000000000)
  directionHi := (425668818520521979529/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree074.table
  base := (16282290032633966989773336875630190576221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2339809222578732038621551709917800000000000000)
      constant := (50213789947137033000516294860654034982307161990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree074.table
  base := (40705725056785756124906116636364795316707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1041848335304446732856864499745800000000000000)
      constant := (22398285063670286780768413543693579022034974992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53208602315065247441/12500000000000000000)
  centralHi := (425668818520521979529/100000000000000000000)
  directionLo := (428574441456448931737/100000000000000000000)
  directionHi := (214287220728224465869/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree075.table
  base := (85249087395426631006657420775358698936739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-263338260747286875074479878315300000000000000)
      constant := (5727770242661436803996063778483251701505268898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree075.table
  base := (17049817471210326159395518371250582272323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-117256921285894922971360096794300000000000000)
      constant := (2554920303063161324403172501176167930798399080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428574441456448931737/100000000000000000000)
  centralHi := (214287220728224465869/50000000000000000000)
  directionLo := (107865124310049025939/25000000000000000000)
  directionHi := (431460497240196103757/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree076.table
  base := (44581642718272181243543985680395597484633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2400279470872431712719086099757600000000000000)
      constant := (52903666936713617622763538796989769184917088108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree076.table
  base := (11145410675661373246571615608303369253933/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1068776247841661880627617242551600000000000000)
      constant := (23598127593181751130741505425490541328336275392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107865124310049025939/25000000000000000000)
  centralHi := (431460497240196103757/100000000000000000000)
  directionLo := (86865475187281941581/20000000000000000000)
  directionHi := (217163687968204853953/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree077.table
  base := (18630808854314981849751933324395096737299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2430514595019281549767853294677500000000000000)
      constant := (54274994205179354210085437370934505307364006810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree077.table
  base := (93154044246772256477731278662203706881179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1082240204110269454512993613954500000000000000)
      constant := (24209819660406704947888948642855278647649043912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86865475187281941581/20000000000000000000)
  centralHi := (217163687968204853953/50000000000000000000)
  directionLo := (437175454819752504737/100000000000000000000)
  directionHi := (218587727409876252369/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree078.table
  base := (24305340972106105750947885459675323400617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-273416635462903487424068943288600000000000000)
      constant := (6184879332128464428787692757333415705199597976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree078.table
  base := (97221363868744378429720059109343815524457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-121744906708764114266485553928600000000000000)
      constant := (2758817658795505754190529359076762801895369944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437175454819752504737/100000000000000000000)
  centralHi := (218587727409876252369/50000000000000000000)
  directionLo := (55000637369305145463/12500000000000000000)
  directionHi := (88001019790888232741/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree079.table
  base := (50682622138622936915296661359800219982349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2490984843312981223865387684517300000000000000)
      constant := (57070426288486167903892466313103514356153826524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree079.table
  base := (50682622130816503710987427332369234827203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1109168116647484602283746356760300000000000000)
      constant := (25456745399372045723288961066518021436696605968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55000637369305145463/12500000000000000000)
  centralHi := (88001019790888232741/20000000000000000000)
  directionLo := (442816661740451741757/100000000000000000000)
  directionHi := (221408330870225870879/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree080.table
  base := (52792842714981359417287573324186315487003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2521219967459831060914154879437200000000000000)
      constant := (58494531103039786749551699645602600255561108228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree080.table
  base := (105585685417578471210539183772076766662897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1122632072916092176169122728163200000000000000)
      constant := (26091979070988163010856617346803363192773129816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442816661740451741757/100000000000000000000)
  centralHi := (221408330870225870879/50000000000000000000)
  directionLo := (445610485428706843743/100000000000000000000)
  directionHi := (13925327669647088867/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree081.table
  base := (109882687339895323093748281683422839152919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-94498336726173366591219336087300000000000000)
      constant := (2219860312322589200414373315948840666456833886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree081.table
  base := (109882687330073575767484497927424931912023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-126232892131633305561611011062900000000000000)
      constant := (2970562215995724485709628708756761171074322216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445610485428706843743/100000000000000000000)
  centralHi := (13925327669647088867/3125000000000000000)
  directionLo := (44838690160737060857/10000000000000000000)
  directionHi := (448386901607370608571/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree082.table
  base := (57128125000733952066308702307485798684629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2581690215753530735011689269277000000000000000)
      constant := (61395518277407108489459611974513364478608159804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree082.table
  base := (57128124996839810785466510514252643566303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1149559985453307323939875470969000000000000000)
      constant := (27385988018253350754687139374483448186681215568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44838690160737060857/10000000000000000000)
  centralHi := (448386901607370608571/100000000000000000000)
  directionLo := (451146231661207548391/100000000000000000000)
  directionHi := (56393278957650943549/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree083.table
  base := (118706373409978582781236213702642270982551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2611925339900380572060456464196900000000000000)
      constant := (62872400637055978246238698189974439242018152938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree083.table
  base := (23741274680760736186991388640892959456907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1163023941721914897825251842371900000000000000)
      constant := (28044763293830915772212766905061715700044165480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451146231661207548391/100000000000000000000)
  centralHi := (56393278957650943549/12500000000000000000)
  directionLo := (56736098400725833261/12500000000000000000)
  directionHi := (453888787205806666089/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree084.table
  base := (15404132195177361653589090309512994272753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-293573384894136712123247073235200000000000000)
      constant := (7151875056843581100761139166443417246352366768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree084.table
  base := (4929322302260954518286518617679805393833/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-130720877554502496856736468197200000000000000)
      constant := (3190153974518473353956809059464310146797893400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56736098400725833261/12500000000000000000)
  centralHi := (453888787205806666089/100000000000000000000)
  directionLo := (228307435249165802341/50000000000000000000)
  directionHi := (456614870498331604683/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree085.table
  base := (127836302452332058888283885020090560230773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2672395588194080246157990854036700000000000000)
      constant := (65878942900960423688395769168173274904981137374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree085.table
  base := (63918151224226085567034396256105357631003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1189951854259130045596004585177700000000000000)
      constant := (29385855448735234355805861464443178603387578768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228307435249165802341/50000000000000000000)
  centralHi := (456614870498331604683/100000000000000000000)
  directionLo := (229662387413164717669/50000000000000000000)
  directionHi := (459324774826329435339/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree086.table
  base := (132516108079701655046652792667964774915389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2702630712340930083206758048956600000000000000)
      constant := (67408602805112182171323392379326469060093008782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree086.table
  base := (33129027019156703203249932566401463641687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1203415810527737619481380956580600000000000000)
      constant := (30068172328016726624768241472957201031351779744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229662387413164717669/50000000000000000000)
  centralHi := (459324774826329435339/100000000000000000000)
  directionLo := (14438087027375431853/3125000000000000000)
  directionHi := (462018784876013819297/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree087.table
  base := (137272474440864092612185832633268903860549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-303651759609753324472836138208500000000000000)
      constant := (7661761691556087412642389138842347686679498318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree087.table
  base := (27454494887685516969346888964670585284331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-135208862977371688151861925331500000000000000)
      constant := (3417592934276895576051669765870286142725950760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14438087027375431853/3125000000000000000)
  centralHi := (462018784876013819297/100000000000000000000)
  directionLo := (232348588540665785993/50000000000000000000)
  directionHi := (464697177081331571987/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree088.table
  base := (28421080306687955614318102249530287449571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2763100960634629757304292438796400000000000000)
      constant := (70520700157600073395003913765484233750581098490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree088.table
  base := (71052700765754671074030851870542247946937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1230343723064952767252133699386400000000000000)
      constant := (31456347690144518840714579059205850286731533872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232348588540665785993/50000000000000000000)
  centralHi := (464697177081331571987/100000000000000000000)
  directionLo := (467360219955024124367/100000000000000000000)
  directionHi := (29210013747189007773/6250000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree089.table
  base := (7350744467763945899835646329781946988853/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2793336084781479594353059633716300000000000000)
      constant := (72103137605863563827989894648115419816144488280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree089.table
  base := (29402977870749927671004321942652687134857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1243807679333560341137510070789300000000000000)
      constant := (32162206172958973795848844824083157394486303480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467360219955024124367/100000000000000000000)
  centralHi := (29210013747189007773/6250000000000000000)
  directionLo := (1468775545008769167/312500000000000000)
  directionHi := (470008174402806133441/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree090.table
  base := (15200093790441880869711657915569532978833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5940000000000000000000000000000000000000000
      center := (23791)
      previous := (0)
      next := (20165)
      square := (1034483252302793802601676964600000000000000)
      linear := (-104576711441789978940808401060600000000000000)
      constant := (2729746946991251117442674974746233025894268020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree090.table
  base := (152000937903207475548165096652040240306503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-139696848400240879446987382465800000000000000)
      constant := (3652879095213509957410888027154478370322750376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1468775545008769167/312500000000000000)
  centralHi := (470008174402806133441/100000000000000000000)
  directionLo := (14770040438178179727/3125000000000000000)
  directionHi := (94528258804340350253/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree091.table
  base := (3141270943581002701192467004724844302663/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2853806333075179268450594023556100000000000000)
      constant := (75320790046271704628105752108007315146305459700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree091.table
  base := (157063547178090763835786510096167978199239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1270735591870775488908262813595100000000000000)
      constant := (33597464742019592286513943415127525973604175592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14770040438178179727/3125000000000000000)
  centralHi := (94528258804340350253/20000000000000000000)
  directionLo := (760415720613606581/160000000000000000)
  directionHi := (237629912691752056563/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree092.table
  base := (162202717177490338127941745780691548559603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2884041457222029105499361218476000000000000000)
      constant := (76956005038360352318909475036012931055798912914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree092.table
  base := (32440543435346122304370611925199412923289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1284199548139383062793639184998000000000000000)
      constant := (34326864828241085945287376606183557076586019960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (760415720613606581/160000000000000000)
  centralHi := (237629912691752056563/50000000000000000000)
  directionLo := (477864008304254817789/100000000000000000000)
  directionHi := (47786400830425481779/10000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree093.table
  base := (167418447898162530579509428068384591703797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-323808509040986549172014268155100000000000000)
      constant := (8734312505000492569387126481089023842416166254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree093.table
  base := (167418447897560973723659030136479772349053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-144184833823110070742112839600100000000000000)
      constant := (3896012457286100869454929497809957604700449976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477864008304254817789/100000000000000000000)
  centralHi := (47786400830425481779/10000000000000000000)
  directionLo := (19218163044023079133/4000000000000000000)
  directionHi := (240227038050288489163/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree094.table
  base := (10794421208723673002808792425326690257813/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2944511705515728779596895608315800000000000000)
      constant := (80279212566180083393033533839371481333676878304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree094.table
  base := (86355369669551253083636074196656805739743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1311127460676598210564391927803800000000000000)
      constant := (35809206604010513159950320793831601922625776208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19218163044023079133/4000000000000000000)
  centralHi := (240227038050288489163/50000000000000000000)
  directionLo := (483030255833637310793/100000000000000000000)
  directionHi := (241515127916818655397/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree095.table
  base := (11129974468770421365490618418245817228417/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-2974746829662578616645662803235700000000000000)
      constant := (81967205101864652518005789259009785167349629536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree095.table
  base := (22259948937493715076135381899177801072797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1324591416945205784449768299206700000000000000)
      constant := (36562148293537883629654795034409980553375176128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483030255833637310793/100000000000000000000)
  centralHi := (241515127916818655397/50000000000000000000)
  directionLo := (24279638427072962089/5000000000000000000)
  directionHi := (485592768541459241781/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree096.table
  base := (183525004379059160622926080816987689115863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17820000000000000000000000000000000000000000
      center := (71373)
      previous := (0)
      next := (60495)
      square := (3103449756908381407805030893800000000000000)
      linear := (-333886883756603161521603333128400000000000000)
      constant := (9296976683559614737831560761369472062004467866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree096.table
  base := (36705000875752146781531515138708866049371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (31783)
      previous := (0)
      next := (26825)
      square := (1379311003070391736802235952800000000000000)
      linear := (-148672819245979262037238296734400000000000000)
      constant := (4146993020460828254575071711526887109555509160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24279638427072962089/5000000000000000000)
  centralHi := (485592768541459241781/100000000000000000000)
  directionLo := (122035457365064935349/25000000000000000000)
  directionHi := (488141829460259741397/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree097.table
  base := (47261744493621311616696808207145411068719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-3035217077956278290743197193075500000000000000)
      constant := (85395967716675022264453866033523554910880461288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree097.table
  base := (23630872246781131993140681170484825816387/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1351519329482420932220521042012500000000000000)
      constant := (38091573275830055042952692684771192332353652288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell188.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122035457365064935349/25000000000000000000)
  centralHi := (488141829460259741397/100000000000000000000)
  directionLo := (98135529647087430819/20000000000000000000)
  directionHi := (30667353014714822131/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree098.table
  base := (194645512285363895245372555073858428319851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160380000000000000000000000000000000000000000
      center := (642357)
      previous := (0)
      next := (544455)
      square := (27931047812175432670245278044200000000000000)
      linear := (-3065452202103128127791964387995400000000000000)
      constant := (87136737795760216561813179761924191473393770338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 859
  qDenominator := 1584
  table := BinomialMassData.Q859_1584.Degree098.table
  base := (194645512285176981567706829401084426374081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (286047)
      previous := (0)
      next := (241425)
      square := (12413799027633525631220123575200000000000000)
      linear := (-1364983285751028506105897413415400000000000000)
      constant := (38868056568576863522649794129483392291194449368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q859_1584.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell188.Kernel098
