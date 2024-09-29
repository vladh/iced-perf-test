#![allow(unused_variables)]

mod grid;
use grid::Grid;

use iced::{Element, Task};

pub fn main() -> iced::Result {
    iced::application("App", App::update, App::view)
        .antialiasing(true)
        .run()
}

#[derive(Debug, Clone)]
enum Message {}

#[derive(Debug)]
struct App {}

impl Default for App {
    fn default() -> Self {
        Self::new()
    }
}

impl App {
    fn new() -> Self {
        App {}
    }

    fn update(&mut self, message: Message) -> Task<Message> {
        Task::none()
    }

    fn view(&self) -> Element<'_, Message> {
        Grid::new().into()
    }
}
