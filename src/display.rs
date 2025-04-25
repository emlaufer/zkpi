use crate::term::{BindingData, Term, TermData, Theorem};
use crossterm::{
    cursor,
    event::{self, Event, KeyCode},
    execute,
    style::{self, Color, Print, ResetColor, SetForegroundColor},
    terminal::{self, ClearType},
};
use std::collections::{HashMap, HashSet};
use std::io::{stdout, Write};

pub fn display_defn_tree(term: &Term, prefix: &str, is_last: bool) {
    let new_prefix = if is_last {
        format!("{}    ", prefix)
    } else {
        format!("{}│   ", prefix)
    };

    match &**term {
        TermData::Defn(name, ty, value) => {
            let branch = if is_last { "└──" } else { "├──" };
            println!("{}{} Defn: {}", prefix, branch, name);
        }
        TermData::App(f, e) => {
            display_defn_tree(f, &new_prefix, false);
            display_defn_tree(e, &new_prefix, true);
        }
        TermData::Binding(BindingData { domain, body, .. }) => {
            display_defn_tree(domain, &new_prefix, false);
            display_defn_tree(body, &new_prefix, true);
        }
        TermData::Proj(_, _, expr) => {
            display_defn_tree(expr, &new_prefix, true);
        }
        _ => {}
    }
}

pub fn display_theorem_trees(theorem: &Theorem) {
    println!("Type Tree:");
    display_defn_tree(&theorem.ty, "", true);

    println!("\nProof Tree:");
    display_defn_tree(&theorem.val, "", true);
}

/// Interactive display for a theorem's definition tree.
pub fn display_theorem_interactive(theorem: &Theorem) {
    // Generate the definition tree from the theorem.
    let root = generate_defn_tree(&theorem.val, "Theorem".to_string(), &mut HashSet::new());

    // Interactive display logic.
    let mut expanded_nodes: HashMap<String, bool> = HashMap::new();
    let mut current_path: Vec<String> = vec![root.name.clone()];
    let mut scroll_offset = 0;

    // Enable raw mode for interactive input.
    terminal::enable_raw_mode().unwrap();
    let mut stdout = stdout();

    loop {
        clear_screen(&mut stdout);
        display_header(&mut stdout);

        // Get terminal size to handle scrolling.
        let (_, terminal_height) = terminal::size().unwrap();
        let visible_height = terminal_height as usize - 10; // Account for header and padding.

        // Collect visible nodes and display the tree.
        let visible_nodes = collect_visible_nodes(&root, &expanded_nodes);
        let current_index = visible_nodes
            .iter()
            .position(|path| *path == current_path)
            .unwrap_or(0);

        // Adjust scroll offset if necessary.
        if current_index < scroll_offset {
            scroll_offset = current_index;
        } else if current_index >= scroll_offset + visible_height {
            scroll_offset = current_index - visible_height + 1;
        }

        display_tree(
            &root,
            &expanded_nodes,
            &current_path,
            0,
            &mut stdout,
            scroll_offset,
            visible_height,
        );

        // Wait for a key event.
        if let Event::Key(key_event) = event::read().unwrap() {
            match key_event.code {
                KeyCode::Char('q') => break, // Quit
                KeyCode::Up => move_up(&mut current_path, &root, &expanded_nodes), // Move up
                KeyCode::Down => move_down(&mut current_path, &root, &expanded_nodes), // Move down
                KeyCode::Enter => toggle_expand(&mut expanded_nodes, &current_path), // Expand/Collapse
                _ => {}
            }
        }
    }

    // Restore terminal to normal mode.
    terminal::disable_raw_mode().unwrap();
}

/// A node in the definition tree.
#[derive(Debug)]
struct TreeNode {
    name: String,
    children: Vec<TreeNode>,
}

/// Recursively generates a tree of definitions (`Defn`) from a `Term`.
fn generate_defn_tree(term: &Term, name: String, visited: &mut HashSet<String>) -> TreeNode {
    // Avoid cycles by skipping already visited definitions.
    if visited.contains(&name) {
        return TreeNode {
            name,
            children: vec![],
        };
    }
    visited.insert(name.clone());

    let mut children = vec![];

    // Recursively traverse the term structure to find all `Defn` nodes.
    fn traverse(term: &Term, visited: &mut HashSet<String>, children: &mut Vec<TreeNode>) {
        match &**term {
            TermData::Defn(defn_name, _, value) => {
                // Add the definition's value to the tree.
                if !visited.contains(defn_name) {
                    children.push(generate_defn_tree(value, defn_name.clone(), visited));
                }
            }
            TermData::App(f, e) => {
                // Traverse function and argument.
                traverse(f, visited, children);
                traverse(e, visited, children);
            }
            TermData::Binding(BindingData { domain, body, .. }) => {
                // Traverse domain and body of the binding.
                traverse(domain, visited, children);
                traverse(body, visited, children);
            }
            TermData::Proj(_, _, expr) => {
                // Traverse the projection's expression.
                traverse(expr, visited, children);
            }
            _ => {}
        }
    }

    traverse(term, visited, &mut children);

    TreeNode { name, children }
}

/// Displays the tree interactively with scrolling and expanded/collapsed indicators.
fn display_tree(
    node: &TreeNode,
    expanded_nodes: &HashMap<String, bool>,
    current_path: &[String],
    depth: usize,
    stdout: &mut impl Write,
    scroll_offset: usize,
    visible_height: usize,
) {
    let visible_nodes = collect_visible_nodes(node, expanded_nodes);
    let start = scroll_offset;
    let end = (scroll_offset + visible_height).min(visible_nodes.len());

    for (index, path) in visible_nodes[start..end].iter().enumerate() {
        let node = find_node_by_path(node, path).unwrap();
        let is_current = path == current_path;
        let is_expanded = *expanded_nodes.get(&node.name).unwrap_or(&false);

        // Indicate expanded/collapsed state with color.
        write!(stdout, "\r{:indent$}", "", indent = (path.len() - 1) * 2).unwrap();
        if is_current {
            write!(stdout, "> ").unwrap();
        } else {
            write!(stdout, "  ").unwrap();
        }

        if is_expanded {
            execute!(stdout, SetForegroundColor(Color::Red)).unwrap();
            write!(stdout, "[-] ").unwrap();
        } else if !node.children.is_empty() {
            execute!(stdout, SetForegroundColor(Color::Green)).unwrap();
            write!(stdout, "[+] ").unwrap();
        } else {
            write!(stdout, "    ").unwrap();
        }

        execute!(stdout, ResetColor).unwrap();
        writeln!(stdout, "{}\r", node.name).unwrap();
    }
}

/// Displays the header with key bindings.
fn display_header(stdout: &mut impl Write) {
    writeln!(stdout, "\rInteractive Theorem Viewer").unwrap();
    writeln!(stdout, "\r--------------------------").unwrap();
    writeln!(stdout, "\rKey Bindings:").unwrap();
    writeln!(stdout, "\r  ↑ / ↓ : Navigate").unwrap();
    writeln!(stdout, "\r  Enter : Expand/Collapse").unwrap();
    writeln!(stdout, "\r  q     : Quit").unwrap();
    writeln!(stdout, "\r").unwrap(); // Add an empty line after the header.
}

/// Moves the current selection up in the tree.
fn move_up(
    current_path: &mut Vec<String>,
    root: &TreeNode,
    expanded_nodes: &HashMap<String, bool>,
) {
    let visible_nodes = collect_visible_nodes(root, expanded_nodes);
    if let Some(current_index) = visible_nodes.iter().position(|path| *path == *current_path) {
        if current_index > 0 {
            *current_path = visible_nodes[current_index - 1].clone();
        }
    }
}

/// Moves the current selection down in the tree.
fn move_down(
    current_path: &mut Vec<String>,
    root: &TreeNode,
    expanded_nodes: &HashMap<String, bool>,
) {
    let visible_nodes = collect_visible_nodes(root, expanded_nodes);
    if let Some(current_index) = visible_nodes.iter().position(|path| *path == *current_path) {
        if current_index + 1 < visible_nodes.len() {
            *current_path = visible_nodes[current_index + 1].clone();
        }
    }
}

/// Toggles the expansion state of the current node.
fn toggle_expand(expanded_nodes: &mut HashMap<String, bool>, current_path: &[String]) {
    let current_node_name = current_path.last().unwrap();
    let is_expanded = expanded_nodes
        .entry(current_node_name.clone())
        .or_insert(false);
    *is_expanded = !*is_expanded;
}

/// Collects all visible nodes in the tree based on the expanded state.
fn collect_visible_nodes(
    node: &TreeNode,
    expanded_nodes: &HashMap<String, bool>,
) -> Vec<Vec<String>> {
    let mut result = vec![vec![node.name.clone()]];
    if *expanded_nodes.get(&node.name).unwrap_or(&false) {
        for child in &node.children {
            let child_paths = collect_visible_nodes(child, expanded_nodes);
            for mut child_path in child_paths {
                let mut full_path = vec![node.name.clone()];
                full_path.append(&mut child_path);
                result.push(full_path);
            }
        }
    }
    result
}

/// Finds a node in the tree by following the given path.
fn find_node_by_path<'a>(root: &'a TreeNode, path: &[String]) -> Option<&'a TreeNode> {
    let mut current = root;
    for name in path.iter().skip(1) {
        if let Some(child) = current.children.iter().find(|c| &c.name == name) {
            current = child;
        } else {
            return None;
        }
    }
    Some(current)
}

/// Clears the terminal screen.
fn clear_screen(stdout: &mut impl Write) {
    execute!(
        stdout,
        terminal::Clear(ClearType::All),
        cursor::MoveTo(0, 0)
    )
    .unwrap();
}
