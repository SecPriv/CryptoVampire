#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MainParser;

type E = Error<Rule>;


struct ParisingEnv {

}