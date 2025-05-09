
rough goals

- [x] Extend `Imp` to integers.
- [x] Extend `Imp` to use partial maps as states, introducing error for undefined variables
- [ ] ~~Use Coq stdlib's partial map to represent state instead of SF's function version~~ On hold until I find a better alternative that is not too complex.
- [x] Make a fuel-based concrete interpreter for ZImp_partial, with correspondence proof to ZImp_partial's bigstep semantics.
- [ ] Define smallstep semantics and show it is sound and complete wrt bigstep and hence the interpreter implementation
- [ ] Define `terminates` in terms of smallstep and fuel
- [ ] Formalize termination checker `check_abs_terminates`
- [ ] Show that `check_abs_terminates(p) -> terminates(p)`