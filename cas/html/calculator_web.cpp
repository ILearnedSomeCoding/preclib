#define main prec_cas_cli_main
#include"../calculator.cpp"
#undef main

#include<emscripten/emscripten.h>

namespace{

calculator_state web_state;
std::string web_result;

}

extern "C"{

EMSCRIPTEN_KEEPALIVE const char *cas_eval(const char *input){
    try{
        if(!input) throw std::invalid_argument("empty input");
        std::string text(input);
        while(!text.empty() && std::isspace((unsigned char)text.back()))
            text.pop_back();
        if(text.empty()) throw std::invalid_argument("empty input");
        if(text == "!help"){
            web_result = help_text();
            return web_result.c_str();
        }
        if(text[0] == '!')
            throw std::invalid_argument(
                "commands are controlled by the web interface");
        web_state.answer = parser(text, web_state).parse();
        collect_garbage(web_state, false);
        web_result = format_answer(web_state.answer);
    }catch(const std::exception &error){
        web_result = std::string("error: ") + error.what();
    }
    return web_result.c_str();
}

EMSCRIPTEN_KEEPALIVE void cas_set_precision(unsigned bits){
    if(bits < 1) bits = 1;
    if(bits > 1048576) bits = 1048576;
    web_state.precision = (double)bits;
}

EMSCRIPTEN_KEEPALIVE unsigned cas_get_precision(){
    return (unsigned)web_state.precision;
}

EMSCRIPTEN_KEEPALIVE unsigned cas_node_count(){
    return (unsigned)std::min<size_t>(web_state.context.node_count(), UINT32_MAX);
}

EMSCRIPTEN_KEEPALIVE void cas_collect(){
    if(web_state.answer.valid())
        web_state.answer = web_state.context.compact(web_state.answer);
}

EMSCRIPTEN_KEEPALIVE void cas_reset(){
    web_state = calculator_state();
    web_result.clear();
}

}
