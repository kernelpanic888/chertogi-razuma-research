# Passport: IF-BS-22F-F8C31D

- Object: finite exact rational measurement table.
- Source: every `RationalParameterNode level` from F8C31A.
- Geometry: F8C31B lift with F8C31C radius `20/(level+1)`.
- Row values: rational `t,v,x,y,s,forward,inverse` plus split error fields.
- Acceptance: all redundant fields recompute exactly; generated rows pass by reduction.
- Decoder: forward and inverse `NoisyUpperReading BlowUpPoint` lists.
- Coverage: both lists cover the exact directional diamond at F8C31C radius.
- Validity: generated measurements have exact zero error.
- Pipeline: F8C29 certificate and F8C28 amplitude interval.
- Red boundary: external acquisition, nonzero empirical errors and signed exchange remain open.
- Next slice: F8C31E, canonical serialized interchange and independently replayable verifier.
