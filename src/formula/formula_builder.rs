use super::formula::{Formula, Variable};

pub trait FormulaBuilder {
    fn formula(&self) -> &Formula;

    fn is_free_variables(&self, var: &Variable) -> bool; 
    fn is_bounded_variable(&self, var: &Variable) -> bool; 

    fn is_used_variable(&self, var: &Variable) -> bool {
        self.is_free_variables(var) || self.is_bounded_variable(var)
    }

    fn is_name_available<'a, 'b>(&'a self, str: &'b str) -> bool;
}