#include <unistd.h>
#include <utility>

#include "./log.hpp"

#if SUBSAT_LOGGING_ENABLED

static LogLevel
get_max_log_level(log::string const& fn, log::string const& pretty_fn)
{
  (void)fn;
  (void)pretty_fn;

  // bool const from_decision_queue = pretty_fn.find("DecisionQueue") != log::string::npos;
  // if (from_decision_queue) {
  //   return LogLevel::Info;
  // }

  // if (pretty_fn.find("add_") != log::string::npos) {
  //   return LogLevel::Info;
  // }

  // if (fn == "analyze") {
  //   return LogLevel::Trace;
  // }
  // if (fn.find("minimize") != log::string::npos) {
  //   return LogLevel::Trace;
  // }
  // if (fn == "propagate_literal") {
  //     return LogLevel::Trace;
  // }

  // return LogLevel::Trace;
  return LogLevel::Warn;
}

/// Filter log messages
bool
subsat_should_log(LogLevel msg_level, log::string fn, log::string pretty_fn)
{
  LogLevel max_log_level = get_max_log_level(fn, pretty_fn);
  return msg_level <= max_log_level;
}

static char const*
level_name(LogLevel msg_level)
{
  switch (msg_level) {
    case LogLevel::Error: return "[ERROR]";
    case LogLevel::Warn:  return "[WARN] ";
    case LogLevel::Info:  return "[INFO] ";
    case LogLevel::Debug: return "[DEBUG]";
    case LogLevel::Trace: return "[TRACE]";
    default:              return "[???]  ";
  }
}

static char const*
level_color(LogLevel msg_level)
{
  switch (msg_level) {
    case LogLevel::Error:
      return "\x1B[31m"; // red
    case LogLevel::Warn:
      return "\x1B[33m"; // yellow
    case LogLevel::Info:
      return "\x1B[34m"; // blue
    default:
      return nullptr;
  }
}

std::pair<std::ostream&, bool>
subsat_log(LogLevel msg_level, log::string fn, log::string /* pretty_fn */)
{
  std::ostream& os = std::cerr;
  int const fd = fileno(stderr);

  size_t width = 20;
  size_t padding = width - std::min(width, fn.size());

  char const* color = level_color(msg_level);
  if (color && !isatty(fd)) { color = nullptr; }

  if (color) { os << color; }
  os << level_name(msg_level) << " [" << fn << "] " << log::string(padding, ' ');
  return {os, (bool)color};
}

#endif  // SUBSAT_LOGGING_ENABLED
